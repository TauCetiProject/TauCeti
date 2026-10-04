/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.ExteriorAlgebra.Corestrict
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced

/-!
# Exterior images of subrepresentations

The image of the exterior power of a subcomodule is a subcomodule of the ambient
exterior power. Over a field, the image of the top exterior power of a finite-dimensional
subcomodule `W` is a line in the ambient `n`th exterior power, where `n = finrank W`.
When the subcomodule is invariant only after restricting to a subgroup, this line still
lies in the restriction of the ambient `n`th exterior-power representation.

This constructs the invariant line used in Chevalley's subspace-to-line passage,
inside a finite-dimensional ambient representation whenever the original representation
is finite-dimensional. It includes the zero subspace, whose determinant line has degree zero.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 4.27 and Lemma 4.28.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
-/

public section

namespace TauCeti.Subcomodule

variable {R H M : Type*} [CommRing R] [CommSemiring H] [Bialgebra R H]
  [Module.Flat R H] [AddCommGroup M] [Module R M] [Comodule R H M]

attribute [local instance] Comodule.exteriorPower

/-- The image of the `n`th exterior power of a subrepresentation in the ambient
exterior representation. -/
noncomputable def exteriorPowerImage (W : Subcomodule R H M) (n : ℕ) :
    Subcomodule R H (⋀[R]^n M) := by
  letI : AddCommGroup W := inferInstanceAs (AddCommGroup W.toSubmodule)
  exact (Comodule.Hom.exteriorPowerMap n (subtype W)).range

/-- The exterior image has the range of the induced exterior-power map as its carrier. -/
@[simp]
theorem exteriorPowerImage_toSubmodule (W : Subcomodule R H M) (n : ℕ) :
    (W.exteriorPowerImage n).toSubmodule =
      LinearMap.range (_root_.exteriorPower.map n W.toSubmodule.subtype) := by
  let : AddCommGroup W := inferInstanceAs (AddCommGroup W.toSubmodule)
  simp only [exteriorPowerImage, Comodule.Hom.range_toSubmodule,
    Comodule.Hom.exteriorPowerMap_toLinearMap, subtype_toLinearMap]
  rfl

/-- Membership in the exterior image is membership in the image of the exterior
power of the underlying subspace. -/
@[simp]
theorem mem_exteriorPowerImage (W : Subcomodule R H M) (n : ℕ) (x : ⋀[R]^n M) :
    x ∈ W.exteriorPowerImage n ↔
      ∃ y : ⋀[R]^n W.toSubmodule, _root_.exteriorPower.map n W.toSubmodule.subtype y = x := by
  rw [← mem_toSubmodule, exteriorPowerImage_toSubmodule]
  rfl

end TauCeti.Subcomodule

namespace TauCeti.Subcomodule

attribute [local instance] Comodule.exteriorPower
  Module.Free.of_divisionRing Module.Flat.of_free

variable {k H M : Type*} [Field k] [CommSemiring H] [Bialgebra k H]
  [AddCommGroup M] [Module k M] [Comodule k H M]

local instance : Module.Flat k H := by
  let : AddCommGroup H := Module.addCommMonoidToAddCommGroup k
  infer_instance

/-- The exterior image of a finite-dimensional subrepresentation has the expected
binomial dimension. -/
@[simp]
theorem finrank_exteriorPowerImage (W : Subcomodule k H M)
    [Module.Finite k W.toSubmodule] (n : ℕ) :
    Module.finrank k (W.exteriorPowerImage n).toSubmodule =
      (Module.finrank k W.toSubmodule).choose n := by
  rw [exteriorPowerImage_toSubmodule,
    LinearMap.finrank_range_of_inj (_root_.exteriorPower.map_injective_field
      W.toSubmodule.injective_subtype), _root_.exteriorPower.finrank_eq]

/-- The top exterior image of a finite-dimensional subrepresentation is a line. -/
theorem finrank_exteriorPowerImage_finrank (W : Subcomodule k H M)
    [Module.Finite k W.toSubmodule] :
    Module.finrank k (W.exteriorPowerImage (Module.finrank k W.toSubmodule)).toSubmodule = 1 := by
  simp [finrank_exteriorPowerImage]

variable {K : Type*} [CommSemiring K] [Bialgebra k K]

local instance : Module.Flat k K := by
  let : AddCommGroup K := Module.addCommMonoidToAddCommGroup k
  infer_instance

/-- A finite-dimensional subrepresentation of a restricted representation determines
an invariant line in the restriction of the ambient `n`th exterior-power representation,
where `n` is the dimension of the subrepresentation. The carrier is the image of its top
exterior power, with no basis choices. -/
theorem exists_line_corestrict_exteriorPower (f : H →ₐc[k] K) :
    letI : Comodule k K M := Comodule.Corestrict f.toCoalgHom
    ∀ W : Subcomodule k K M, Module.Finite k W.toSubmodule →
      let n := Module.finrank k W.toSubmodule
      letI : Comodule k H (⋀[k]^n M) := Comodule.exteriorPower k H M n
      letI : Comodule k K (⋀[k]^n M) := Comodule.Corestrict f.toCoalgHom
      ∃ L : Subcomodule k K (⋀[k]^n M),
        L.toSubmodule = LinearMap.range (_root_.exteriorPower.map n W.toSubmodule.subtype) ∧
        Module.finrank k L.toSubmodule = 1 := by
  let : Comodule k K M := Comodule.Corestrict f.toCoalgHom
  intro W hW
  let : Module.Finite k W.toSubmodule := hW
  let n := Module.finrank k W.toSubmodule
  let E := W.exteriorPowerImage n
  have hEsub := W.exteriorPowerImage_toSubmodule n
  have hEfin := W.finrank_exteriorPowerImage_finrank
  let S := E.toSubmodule
  have hstable (x : ⋀[k]^n M) (hx : x ∈ S) :
      (Comodule.exteriorPower k K M n).coact x ∈
        LinearMap.range (TensorProduct.map S.subtype (LinearMap.id : K →ₗ[k] K)) :=
    E.coact_mem hx
  let : Comodule k H (⋀[k]^n M) := Comodule.exteriorPower k H M n
  let : Comodule k K (⋀[k]^n M) := Comodule.Corestrict f.toCoalgHom
  have hcoact := congrArg (fun c : Comodule k K (⋀[k]^n M) ↦ c.coact)
    (Comodule.exteriorPower_corestrict f n)
  let L : Subcomodule k K (⋀[k]^n M) :=
    ofSubmodule S fun x hx ↦ by
      rw [← hcoact]
      exact hstable x hx
  have hLS : L.toSubmodule = S := by
    ext x
    simp only [mem_toSubmodule, L, mem_ofSubmodule]
  refine ⟨L, ?_, ?_⟩
  · rw [hLS]
    exact hEsub
  · rw [hLS]
    exact hEfin

end TauCeti.Subcomodule
