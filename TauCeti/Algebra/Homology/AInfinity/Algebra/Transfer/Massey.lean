/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Massey
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Cohomology

/-!
# The ternary operation of the minimal model and triple Massey products

Over a field, let `i`, `p`, `h` be the inclusion, projection and homotopy of the contraction of
an `A∞` algebra onto its cohomology, and let `m₃^H` be the ternary operation of the transferred
minimal model.  If `x y = 0` and `y z = 0`, the cochains `u = h m₂ (i x, i y)` and
`v = h m₂ (i y, i z)` bound the products of the representatives, since `m₁ h = 1 - i p` on cycles
and `p` sends a cycle to its class.  So `(i x, i y, i z, u, v)` is a defining system for
`⟨x, y, z⟩`, and the Kontsevich--Soibelman/Merkulov formula for `m₃^H` is exactly the projection of
its Massey cycle.  Hence `m₃^H (x, y, z)` is an element of the triple Massey product, which is
therefore the coset of `m₃^H (x, y, z)` by the indeterminacy `τx · H + H · z`.

The element selected depends on the chosen contraction; only its coset is intrinsic.  The minimal
model therefore refines, but does not replace, the multivalued Massey product.

## Main results

* `TauCeti.AInfinityAlgebra.minimalModel_m_three_mem_tripleMasseyProduct`: the ternary operation of
  the minimal model lies in the triple Massey product.
* `TauCeti.AInfinityAlgebra.mem_tripleMasseyProduct_iff_sub_minimalModel_m_three_mem`: the triple
  Massey product is the coset of the ternary operation of the minimal model by the indeterminacy.

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

/-- The inclusion of the cohomology contraction has degree zero, so it commutes with the Koszul
twist. -/
private theorem cohomologyContraction_incl_koszulTwist (x : 𝒜.Cohomology) :
    𝒜.cohomologyContraction.incl (𝒜.cohomologyGrading.koszulTwist 1 x) =
      𝒜.grading.koszulTwist 1 (𝒜.cohomologyContraction.incl x) := by
  simpa using
    (LinearMap.congr_fun (𝒜.isHomogeneous_cohomologyContraction_incl.koszulTwist_comp 1) x).symm

/-- The homotopy of the cohomology contraction bounds every cycle with vanishing class. -/
private theorem m_one_cohomologyContraction_homotopy {w : A} (hw : w ∈ 𝒜.cycles)
    (h₀ : 𝒜.cohomologyClass hw = 0) :
    𝒜.m 1 ![𝒜.cohomologyContraction.homotopy w] = w := by
  have h := LinearMap.congr_fun 𝒜.cohomologyContraction.dM_comp_homotopy_add_homotopy_comp_dM w
  have hd : 𝒜.differential w = 0 := by rw [differential_apply, ← mem_cycles]; exact hw
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    hd, map_zero, add_zero, 𝒜.cohomologyContraction_proj_of_mem_cycles hw, h₀,
    sub_zero] at h
  rwa [differential_apply] at h

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

end TauCeti.AInfinityAlgebra
