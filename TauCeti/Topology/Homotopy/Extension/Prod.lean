/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Cube
public import TauCeti.Topology.Homotopy.Extension.NDRPair

/-!
# Products of closed cofibrations

If closed subsets `A ⊆ X` and `B ⊆ Y` have the homotopy extension property, then so does
`A × Y ∪ X × B ⊆ X × Y` (Strøm's product theorem). No compactness or separation hypothesis is
needed. The proof passes through NDR data: closed cofibrations are exactly the subsets admitting
NDR data (`TauCeti.nonempty_ndrPair_iff`), and NDR pairs have products (`TauCeti.NDRPair.prod`).
Both subsets are assumed closed here, as NDR data requires; Strøm's theorem needs only one of
them closed.

Two special cases are recorded.

* Taking `B = ∅`, the product `Y × A ⊆ Y × X` of a closed cofibration with any space is a
  cofibration. This allows homotopies to be extended continuously in additional parameters, in
  particular when proving the homotopy lifting property of restriction between compact-open
  mapping spaces.
* Taking `{0, 1} ⊆ I` as the first factor, `{0, 1} × X ∪ I × A ⊆ I × X` is a cofibration: a
  homotopy of maps out of `X × I` may be prescribed at both ends and over `A` at once. This is the
  form in which homotopies between homotopies are extended, as in the proof that a homotopy
  equivalence between cofibrations under `A` is a homotopy equivalence relative to `A`.

## Main declarations

* `TauCeti.HasHomotopyExtensionProperty.prod_univ_union_univ_prod`: **Strøm's product theorem**
  for closed cofibrations.
* `TauCeti.HasHomotopyExtensionProperty.univ_prod`: products with arbitrary spaces.
* `TauCeti.HasHomotopyExtensionProperty.zero_one_prod_univ_union_univ_prod`: the cylinder on a
  closed cofibration, relative to both of its ends.

## References

* A. Strøm, *Note on cofibrations II*, Math. Scand. 22 (1968), 130–142, for the product theorem.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Proposition 0.19, where the cylinder case is used.
* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I, homotopy extension and cofibrations.
-/

public section

open Set unitInterval

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y}

/-- **Strøm's product theorem**: if closed subsets `A ⊆ X` and `B ⊆ Y` have the homotopy
extension property, then so does `A × Y ∪ X × B ⊆ X × Y`. -/
theorem HasHomotopyExtensionProperty.prod_univ_union_univ_prod (hA : HasHomotopyExtensionProperty A)
    (hA' : IsClosed A) (hB : HasHomotopyExtensionProperty B) (hB' : IsClosed B) :
    HasHomotopyExtensionProperty (A ×ˢ (univ : Set Y) ∪ (univ : Set X) ×ˢ B) := by
  obtain ⟨N⟩ := nonempty_ndrPair_iff.2 ⟨hA', hA⟩
  obtain ⟨M⟩ := nonempty_ndrPair_iff.2 ⟨hB', hB⟩
  exact (N.prod M).hasHomotopyExtensionProperty

/-- A closed cofibration remains a cofibration after taking its product with any space. -/
theorem HasHomotopyExtensionProperty.univ_prod (h : HasHomotopyExtensionProperty A)
    (hA : IsClosed A) : HasHomotopyExtensionProperty ((univ : Set Y) ×ˢ A) := by
  simpa using hasHomotopyExtensionProperty_empty.prod_univ_union_univ_prod isClosed_empty h hA

/-- **The cylinder on a closed cofibration**: if a closed subset `A ⊆ X` has the homotopy
extension property, then so does `{0, 1} × X ∪ I × A ⊆ I × X`. -/
theorem HasHomotopyExtensionProperty.zero_one_prod_univ_union_univ_prod
    (h : HasHomotopyExtensionProperty A) (hA : IsClosed A) :
    HasHomotopyExtensionProperty (({0, 1} : Set I) ×ˢ (univ : Set X) ∪ univ ×ˢ A) :=
  hasHomotopyExtensionProperty_zero_one.prod_univ_union_univ_prod (toFinite _).isClosed h hA

end TauCeti
