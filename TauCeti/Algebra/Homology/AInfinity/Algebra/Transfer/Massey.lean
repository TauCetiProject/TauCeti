/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Massey.Higher
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Cohomology

/-!
# The higher operations of the minimal model and Massey products

Over a field, let `i`, `p`, `h` be the inclusion, projection and homotopy of the contraction of
an `A∞` algebra onto its cohomology, and let `m₃^H` be the ternary operation of the transferred
minimal model.  If `x y = 0` and `y z = 0`, the cochains `u = h m₂ (i x, i y)` and
`v = h m₂ (i y, i z)` bound the products of the representatives, since `m₁ h = 1 - i p` on cycles
and `p` sends a cycle to its class.  So `(i x, i y, i z, u, v)` is a defining system for
`⟨x, y, z⟩`, and the Kontsevich--Soibelman/Merkulov formula for `m₃^H` is exactly the projection of
its Massey cycle.  Hence `m₃^H (x, y, z)` is an element of the triple Massey product, which is
therefore the coset of `m₃^H (x, y, z)` by the indeterminacy `τx · H + H · z`.  For classes of
degrees `p`, `q`, `r`, `m₃^H (x, y, z)` has degree `p + q + r - 1`, so it is the value of a
homogeneous defining system, and May's triple Massey product is its coset by
`x · H^{q + r - 1} + H^{p + q - 1} · z`.

The element selected depends on the chosen contraction; only its coset is intrinsic.  The minimal
model therefore refines, but does not replace, the multivalued Massey product.

The same holds in every arity.  If the suspended Taylor map of the minimal model vanishes on every
proper block `x_a ⋯ x_{a+b-1}` of length at least two of the classes `x₀, …, x_{n+1}`, then its
value on the whole word, which is `m_{n+2}` with the Koszul twists of
`TauCeti.AInfinityAlgebra.taylor_of_tprod`, lies in the higher Massey product
`⟨x₀, …, x_{n+1}⟩` of `TauCeti.Algebra.Homology.AInfinity.Algebra.Massey.Higher`.  The defining
system consists of the Taylor components of the inclusion of the minimal model on the proper
blocks.

## Main results

* `TauCeti.AInfinityAlgebra.minimalModel_m_three_mem_tripleMasseyProduct`: the ternary operation of
  the minimal model lies in the triple Massey product.
* `TauCeti.AInfinityAlgebra.mem_tripleMasseyProduct_iff_sub_minimalModel_m_three_mem`: the triple
  Massey product is the coset of the ternary operation of the minimal model by the indeterminacy.
* `TauCeti.AInfinityAlgebra.exists_isHomogeneous_value_eq_minimalModel_m_three`: for homogeneous
  classes, the ternary operation of the minimal model is the value of a homogeneous defining system.
* `TauCeti.AInfinityAlgebra.exists_isHomogeneous_value_eq_iff_sub_minimalModel_m_three`: May's
  triple Massey product is the coset of the ternary operation of the minimal model by the classical
  indeterminacy.
* `TauCeti.AInfinityAlgebra.minimalModel_taylor_subword_mem_masseyProduct`: the higher operations
  of the minimal model lie in the higher Massey products, once the lower operations vanish on the
  proper blocks.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.3.
* D.-M. Lu, J. H. Palmieri, Q.-S. Wu, J. J. Zhang, *A-infinity structure on Ext-algebras*,
  J. Pure Appl. Algebra 213 (2009), Theorem 3.1.
-/

public section

namespace TauCeti.AInfinityAlgebra

universe uK uA

variable {K : Type uK} {A : Type uA} [Field K] [AddCommGroup A] [Module K A]
  (𝒜 : AInfinityAlgebra K A)

/-- **The ternary operation of the minimal model lies in the triple Massey product.**  If
`x y = 0` and `y z = 0`, then `m₃^H (x, y, z)` is the value of the defining system formed by the
chosen representatives `i x`, `i y`, `i z` and the cochains `h m₂ (i x, i y)`, `h m₂ (i y, i z)`. -/
theorem minimalModel_m_three_mem_tripleMasseyProduct {x y z : 𝒜.Cohomology} (hxy : x * y = 0)
    (hyz : y * z = 0) : 𝒜.minimalModel.m 3 ![x, y, z] ∈ 𝒜.tripleMasseyProduct x y z := by
  have hi := 𝒜.cohomologyContraction_incl_mem_cycles
  have hab := 𝒜.m_two_mem_cycles (hi x) (hi y)
  have hbc := 𝒜.m_two_mem_cycles (hi y) (hi z)
  have hab₀ : 𝒜.cohomologyClass hab = 0 := by
    rw [← 𝒜.cohomologyMul_cohomologyClass (hi x) (hi y), cohomologyClass_cohomologyContraction_incl,
      cohomologyClass_cohomologyContraction_incl, ← cohomology_mul_eq_cohomologyMul, hxy]
  have hbc₀ : 𝒜.cohomologyClass hbc = 0 := by
    rw [← 𝒜.cohomologyMul_cohomologyClass (hi y) (hi z), cohomologyClass_cohomologyContraction_incl,
      cohomologyClass_cohomologyContraction_incl, ← cohomology_mul_eq_cohomologyMul, hyz]
  let S : 𝒜.TripleMasseyDefiningSystem x y z :=
    { a := 𝒜.cohomologyContraction.incl x
      b := 𝒜.cohomologyContraction.incl y
      c := 𝒜.cohomologyContraction.incl z
      u := 𝒜.cohomologyContraction.homotopy
        (𝒜.m 2 ![𝒜.cohomologyContraction.incl x, 𝒜.cohomologyContraction.incl y])
      v := 𝒜.cohomologyContraction.homotopy
        (𝒜.m 2 ![𝒜.cohomologyContraction.incl y, 𝒜.cohomologyContraction.incl z])
      a_mem_cycles := hi x
      b_mem_cycles := hi y
      c_mem_cycles := hi z
      cohomologyClass_a := 𝒜.cohomologyClass_cohomologyContraction_incl x
      cohomologyClass_b := 𝒜.cohomologyClass_cohomologyContraction_incl y
      cohomologyClass_c := 𝒜.cohomologyClass_cohomologyContraction_incl z
      m_one_u := 𝒜.m_one_cohomologyContraction_homotopy hab hab₀
      m_one_v := 𝒜.m_one_cohomologyContraction_homotopy hbc hbc₀ }
  refine mem_tripleMasseyProduct.mpr ⟨S, ?_⟩
  rw [TripleMasseyDefiningSystem.value_def, minimalModel_m_three,
    ← cohomologyContraction_proj_of_mem_cycles _ S.cycle_mem_cycles,
    TripleMasseyDefiningSystem.cycle_def, cohomologyContraction_incl_koszulTwist]
  simp only [S, map_add, map_sub]
  abel

/-- **The triple Massey product is a coset of the minimal-model ternary operation**: if `x y = 0`
and `y z = 0`, then `w` lies in `⟨x, y, z⟩` exactly when `w - m₃^H (x, y, z)` lies in the
indeterminacy `τx · H + H · z`. -/
theorem mem_tripleMasseyProduct_iff_sub_minimalModel_m_three_mem {x y z w : 𝒜.Cohomology}
    (hxy : x * y = 0) (hyz : y * z = 0) :
    w ∈ 𝒜.tripleMasseyProduct x y z ↔
      w - 𝒜.minimalModel.m 3 ![x, y, z] ∈ 𝒜.tripleMasseyIndeterminacy x z :=
  mem_tripleMasseyProduct_iff_sub_mem (𝒜.minimalModel_m_three_mem_tripleMasseyProduct hxy hyz)

/-- **For homogeneous classes, `m₃^H` selects an element of May's triple Massey product.**  If `x`,
`y`, `z` have degrees `p`, `q`, `r`, with `x y = 0` and `y z = 0`, then `m₃^H (x, y, z)` is the
value of a defining system homogeneous of degrees `p`, `q`, `r`. -/
theorem exists_isHomogeneous_value_eq_minimalModel_m_three {x y z : 𝒜.Cohomology} {p q r : ℤ}
    (hx : x ∈ 𝒜.cohomologyGrading.piece p) (hy : y ∈ 𝒜.cohomologyGrading.piece q)
    (hz : z ∈ 𝒜.cohomologyGrading.piece r) (hxy : x * y = 0) (hyz : y * z = 0) :
    ∃ S : 𝒜.TripleMasseyDefiningSystem x y z,
      S.IsHomogeneous p q r ∧ S.value = 𝒜.minimalModel.m 3 ![x, y, z] := by
  refine (exists_isHomogeneous_value_eq_iff hx hy hz).2
    ⟨𝒜.minimalModel_m_three_mem_tripleMasseyProduct hxy hyz, ?_⟩
  -- The ternary operation of the minimal model has degree `-1`.
  rw [← minimalModel_grading] at hx hy hz ⊢
  exact 𝒜.minimalModel.m_three_mem_piece hx hy hz

/-- **May's triple Massey product is the coset of `m₃^H` by the classical indeterminacy**: for
classes `x`, `y`, `z` of degrees `p`, `q`, `r` with `x y = 0` and `y z = 0`, `w` is the value of a
defining system homogeneous of degrees `p`, `q`, `r` exactly when `w - m₃^H (x, y, z)` lies in
`x · H^{q + r - 1} + H^{p + q - 1} · z`. -/
theorem exists_isHomogeneous_value_eq_iff_sub_minimalModel_m_three {x y z w : 𝒜.Cohomology}
    {p q r : ℤ} (hx : x ∈ 𝒜.cohomologyGrading.piece p) (hy : y ∈ 𝒜.cohomologyGrading.piece q)
    (hz : z ∈ 𝒜.cohomologyGrading.piece r) (hxy : x * y = 0) (hyz : y * z = 0) :
    (∃ S : 𝒜.TripleMasseyDefiningSystem x y z, S.IsHomogeneous p q r ∧ S.value = w) ↔
      ∃ s ∈ 𝒜.cohomologyGrading.piece (q + r - 1), ∃ t ∈ 𝒜.cohomologyGrading.piece (p + q - 1),
        x * s + t * z = w - 𝒜.minimalModel.m 3 ![x, y, z] :=
  exists_isHomogeneous_value_eq_iff_sub_mem hx hy hz
    (𝒜.exists_isHomogeneous_value_eq_minimalModel_m_three hx hy hz hxy hyz)

/-- **The higher operations of the minimal model select elements of higher Massey products.**
If the suspended Taylor map of the minimal model vanishes on every proper block of length at least
two of the classes `x₀, …, x_{n+1}`, then its value on the whole word `x₀ ⋯ x_{n+1}` lies in the
Massey product `⟨x₀, …, x_{n+1}⟩`. -/
theorem minimalModel_taylor_subword_mem_masseyProduct {n : ℕ} {x : Fin (n + 2) → 𝒜.Cohomology}
    (hx : ∀ a b, 2 ≤ b → b ≤ n + 1 → a + b ≤ n + 2 →
      𝒜.minimalModel.taylor (ReducedTensorWords.subword K x a b) = 0) :
    𝒜.minimalModel.taylor (ReducedTensorWords.subword K x 0 (n + 2)) ∈ 𝒜.masseyProduct x := by
  -- On blocks of length one the Taylor map is the unary operation, which vanishes.
  have hy : ∀ a b, 0 < b → b ≤ n + 1 → a + b ≤ n + 2 →
      𝒜.minimalModel.taylor (ReducedTensorWords.subword K x a b) = 0 := by
    intro a b hb hbn hab
    rcases Nat.lt_or_ge b 2 with h | h
    · obtain rfl : b = 1 := by omega
      rw [ReducedTensorWords.subword_one K _ x (by omega), taylor_ofLetter]
      exact 𝒜.isMinimal_minimalModel.m_one _
    · exact hx a b h hbn hab
  have hincl : ∀ z, 𝒜.minimalModelInclusion.linearPart z ∈ 𝒜.cycles := fun z ↦ by
    rw [linearPart_minimalModelInclusion]
    exact 𝒜.cohomologyContraction_incl_mem_cycles z
  -- The inclusion of the minimal model induces the identity on cohomology.
  have hclass : ∀ z, 𝒜.cohomologyClass (hincl z) = z := fun z ↦
    (𝒜.cohomologyClass_congr _ (𝒜.cohomologyContraction_incl_mem_cycles z)
      (by rw [linearPart_minimalModelInclusion])).trans
        (𝒜.cohomologyClass_cohomologyContraction_incl z)
  simpa only [hclass] using
    𝒜.minimalModelInclusion.cohomologyClass_mem_masseyProduct hy

end TauCeti.AInfinityAlgebra
