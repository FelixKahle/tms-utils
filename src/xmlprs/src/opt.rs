// Copyright 2025 Felix Kahle. All rights reserved.

/// A policy for matching XML elements and attributes.
///
/// This policy is used to determine how XML elements and attributes are compared
/// for equality. It allows for different matching strategies, such as strict
/// case-sensitive matching, case-insensitive matching or a custom matching function.
///
/// # Type Parameters
///
/// * `F`: A function type that takes two string slices and returns a boolean.
///
/// # Example
///
/// ```rust
/// use xmlprs::opt::XmlMatchPolicy;
///
/// let strict_policy: XmlMatchPolicy<fn(&str, &str) -> bool> = XmlMatchPolicy::strict();
/// let case_insensitive_policy: XmlMatchPolicy<fn(&str, &str) -> bool> = XmlMatchPolicy::case_insensitive();
///
/// assert!(strict_policy.matches("Element", "Element"));
/// assert!(!strict_policy.matches("Element", "element"));
/// assert!(case_insensitive_policy.matches("Element", "element"));
/// assert!(!case_insensitive_policy.matches("Element", "Different"));
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct XmlMatchPolicy<F>
where
    F: Fn(&str, &str) -> bool,
{
    matcher: F,
}

impl<F> XmlMatchPolicy<F>
where
    F: Fn(&str, &str) -> bool,
{
    /// Creates a new `XmlMatchPolicy` with the given matcher function.
    ///
    /// # Arguments
    ///
    /// * `matcher`: A function that takes two string slices
    /// and returns a boolean indicating if they match.
    ///
    /// # Returns
    ///
    /// An instance of `XmlMatchPolicy` with the provided matcher.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xmlprs::opt::XmlMatchPolicy;
    ///
    /// let custom_policy = XmlMatchPolicy::new(|a, b| a.len() == b.len());
    /// assert!(custom_policy.matches("test", "aaaa"));
    /// assert!(!custom_policy.matches("test", "test123"));
    /// ```
    pub fn new(matcher: F) -> Self {
        XmlMatchPolicy { matcher }
    }

    /// Returns a reference to the matcher function used by this policy.
    ///
    /// # Returns
    ///
    /// A reference to the matcher function that takes two string slices
    ///
    /// # Example
    ///
    /// ```rust
    /// use xmlprs::opt::XmlMatchPolicy;
    ///
    /// let policy: XmlMatchPolicy<fn(&str, &str) -> bool> = XmlMatchPolicy::strict();
    /// assert_eq!(policy.matcher()("Element", "Element"), true);
    /// assert_eq!(policy.matcher()("Element", "element"), false);
    /// assert_eq!(policy.matcher()("Element", "Different"), false);
    /// ```
    pub fn matcher(&self) -> &F {
        &self.matcher
    }

    /// Checks if two strings match according to the policy's matcher function.
    ///
    /// # Arguments
    ///
    /// * `a`: The first string to compare.
    /// * `b`: The second string to compare.
    ///
    /// # Returns
    ///
    /// `true` if the strings match according to the policy, `false` otherwise.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xmlprs::opt::XmlMatchPolicy;
    ///
    /// let policy: XmlMatchPolicy<fn(&str, &str) -> bool> = XmlMatchPolicy::case_insensitive();
    /// assert!(policy.matches("Element", "element"));
    /// assert!(!policy.matches("Element", "Different"));
    /// assert!(policy.matches("Element", "ELEMENT"));
    /// ```
    pub fn matches(&self, a: &str, b: &str) -> bool {
        (self.matcher)(a, b)
    }
}

impl XmlMatchPolicy<fn(&str, &str) -> bool> {
    /// Creates a strict matching policy that checks for exact equality.
    ///
    /// # Returns
    ///
    /// An instance of `XmlMatchPolicy` that uses strict equality for matching.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xmlprs::opt::XmlMatchPolicy;
    ///
    /// let strict_policy: XmlMatchPolicy<fn(&str, &str) -> bool> = XmlMatchPolicy::strict();
    /// assert!(strict_policy.matches("Element", "Element"));
    /// assert!(!strict_policy.matches("Element", "element"));
    /// assert!(!strict_policy.matches("Element", "Different"));
    /// ```
    pub fn strict() -> XmlMatchPolicy<fn(&str, &str) -> bool> {
        XmlMatchPolicy::new(|a, b| a == b)
    }

    /// Creates a case-insensitive matching policy that ignores ASCII case.
    ///
    /// # Returns
    ///
    /// An instance of `XmlMatchPolicy` that uses case-insensitive matching.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xmlprs::opt::XmlMatchPolicy;
    ///
    /// let case_insensitive_policy: XmlMatchPolicy<fn(&str, &str) -> bool> = XmlMatchPolicy::case_insensitive();
    /// assert!(case_insensitive_policy.matches("Element", "element"));
    /// assert!(!case_insensitive_policy.matches("Element", "Different"));
    /// assert!(case_insensitive_policy.matches("Element", "ELEMENT"));
    /// ```
    pub fn case_insensitive() -> XmlMatchPolicy<fn(&str, &str) -> bool> {
        XmlMatchPolicy::new(|a, b| a.eq_ignore_ascii_case(b))
    }
}

impl Default for XmlMatchPolicy<fn(&str, &str) -> bool> {
    fn default() -> Self {
        XmlMatchPolicy::strict()
    }
}

/// Options for configuring the XML deserializer.
///
/// This struct allows customization of how XML elements and attributes are matched
/// during deserialization. It uses `XmlMatchPolicy` to define the matching behavior
/// for both elements and attributes.
///
/// # Type Parameters
///
/// * `F1`: A function type for matching XML elements.
/// * `F2`: A function type for matching XML attributes.
///
/// # Example
///
/// ```rust
/// use xmlprs::opt::{XmlDeserializerOptions, XmlMatchPolicy};
///
/// let element_match_policy = XmlMatchPolicy::strict();
/// let attribute_match_policy = XmlMatchPolicy::case_insensitive();
///
/// let options = XmlDeserializerOptions::new(element_match_policy, attribute_match_policy);
/// assert!(options.element_match_policy().matches("Element", "Element"));
/// assert!(options.attribute_match_policy().matches("Attribute", "attribute"));
/// ```
pub struct XmlDeserializerOptions<F1, F2>
where
    F1: Fn(&str, &str) -> bool,
    F2: Fn(&str, &str) -> bool,
{
    element_match_policy: XmlMatchPolicy<F1>,
    attribute_match_policy: XmlMatchPolicy<F2>,
}

impl<F1, F2> XmlDeserializerOptions<F1, F2>
where
    F1: Fn(&str, &str) -> bool,
    F2: Fn(&str, &str) -> bool,
{
    /// Creates a new `XmlDeserializerOptions` with the specified match policies.
    ///
    /// # Arguments
    ///
    /// * `element_match_policy`: A policy for matching XML elements.
    /// * `attribute_match_policy`: A policy for matching XML attributes.
    ///
    /// # Returns
    ///
    /// An instance of `XmlDeserializerOptions`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xmlprs::opt::{XmlDeserializerOptions, XmlMatchPolicy};
    ///
    /// let element_match_policy: XmlMatchPolicy<fn(&str, &str) -> bool> = XmlMatchPolicy::strict();
    /// let attribute_match_policy: XmlMatchPolicy<fn(&str, &str) -> bool> = XmlMatchPolicy::case_insensitive();
    ///
    /// let options = XmlDeserializerOptions::new(element_match_policy, attribute_match_policy);
    /// assert!(options.element_match_policy().matches("Element", "Element"));
    /// assert!(options.attribute_match_policy().matches("Attribute", "attribute"));
    ///
    pub fn new(
        element_match_policy: XmlMatchPolicy<F1>,
        attribute_match_policy: XmlMatchPolicy<F2>,
    ) -> Self {
        XmlDeserializerOptions {
            element_match_policy,
            attribute_match_policy,
        }
    }

    /// Returns the element match policy.
    ///
    /// # Returns
    ///
    /// A reference to the `XmlMatchPolicy` used for matching XML elements.
    pub fn element_match_policy(&self) -> &XmlMatchPolicy<F1> {
        &self.element_match_policy
    }

    /// Returns the attribute match policy.
    ///
    /// # Returns
    ///
    /// A reference to the `XmlMatchPolicy` used for matching XML attributes.
    pub fn attribute_match_policy(&self) -> &XmlMatchPolicy<F2> {
        &self.attribute_match_policy
    }
}

impl Default for XmlDeserializerOptions<fn(&str, &str) -> bool, fn(&str, &str) -> bool> {
    fn default() -> Self {
        XmlDeserializerOptions {
            element_match_policy: XmlMatchPolicy::strict(),
            attribute_match_policy: XmlMatchPolicy::strict(),
        }
    }
}

/// Default options for the XML deserializer.
type DefaultXmlDeserializerOptions =
    XmlDeserializerOptions<fn(&str, &str) -> bool, fn(&str, &str) -> bool>;
