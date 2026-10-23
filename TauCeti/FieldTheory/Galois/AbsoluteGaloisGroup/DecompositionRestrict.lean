/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Map
import Mathlib.Topology.Algebra.OpenSubgroup
import TauCeti.Topology.Algebra.Group.TopologicalAbelianization.Lift

/-!
# Restricting the abelianized absolute Galois group of an extension to a finite normal layer

Let `F/K` be a field extension, not necessarily algebraic, and `L/K` a finite normal extension.
Every `K`-embedding `j : L →ₐ[K] Fᵃˡᵍ` into an algebraic closure of `F` has a `G_F`-stable image,
because `L/K` is normal, so an automorphism `τ ∈ G_F = Gal(Fᵃˡᵍ/F)` induces the automorphism `σ` of
`L/K` with `j ∘ σ = τ ∘ j` (`AlgHom.restrictNormalHom`). The map `τ ↦ σ` depends on `j`, but two
embeddings differ by an automorphism of `L/K` and the two maps by conjugation by it
(`AlgHom.restrictNormalHom_comp`), which `Gal(L/K)^ab` does not see. The kernel is open, since `τ`
fixes `j(L)` once it fixes the images of a `K`-basis of `L`; so the map factors through the
topological abelianization `G_F^ab`, and gives a homomorphism

```text
decompositionRestrict K F L : G_F^ab →* Gal(L/K)^ab,   [τ] ↦ [σ]   whenever j ∘ σ = τ ∘ j,
```

for every `j` (`decompositionRestrict_mk`). When `K` is a number field and `F = K_v` a completion,
a `K`-embedding `j` of `L` into `K_vᵃˡᵍ` is a place of `L` above `v`, and the image of `G_{K_v}` in
`Gal(L/K)` is the decomposition group of that place. The absolute local Artin map of `K_v` takes
values in `G_{K_v}^ab`, so `decompositionRestrict` is the map that reads a local Artin symbol in
`Gal(L/K)^ab`, as the local–global compatibility of a global reciprocity map requires; the same
construction serves the finite and the infinite places.

The global theory works with the separable closure `Kˢ`, through the maps
`TauCeti.absoluteGaloisGroupMap τ : G_F → G_K` attached to embeddings `τ : Kˢ →ₐ[K] Fˢ`. Read along
any such `τ` and any embedding `iota` of `L` into `Kˢ`, `decompositionRestrict` is restriction to
`L` (`decompositionRestrict_mk_eq_restrictNormalHom_absoluteGaloisGroupMap`).

## Main definitions

* `TauCeti.decompositionRestrict K F L`: the homomorphism `G_F^ab →* Gal(L/K)^ab`.

## Main results

* `AlgHom.isOpen_ker_restrictNormalHom_comp_restrictScalarsHom`: restriction of
  `Gal(Ω/F)` to `Gal(L/K)` along an embedding of `L` into an algebraic extension `Ω` of `F` has
  open kernel.
* `TauCeti.decompositionRestrict_mk`: the class of `τ` goes to the class of the automorphism `σ`
  of `L` with `j ∘ σ = τ ∘ j`, for every `K`-embedding `j : L →ₐ[K] Fᵃˡᵍ`.
* `TauCeti.decompositionRestrict_mk_eq_restrictNormalHom`: the value on the class of `τ`, as the
  class of the restriction of `τ` along a chosen `j`.
* `TauCeti.decompositionRestrict_mk_eq_restrictNormalHom_absoluteGaloisGroupMap`: the comparison
  with restriction along the separable closures.
* `TauCeti.decompositionRestrict_comp`: compatibility with restriction to a normal subextension.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §9 (decomposition groups and completions)
  and Chapter VI, §5 (local–global compatibility of the reciprocity map).
* J. S. Milne, *Class Field Theory*, Chapter V, §5, and Chapter VII, §5.
-/

public section

noncomputable section

namespace TauCeti

/-! ### Openness of the kernel of restriction -/

/-- Let `Ω/F` be algebraic, `F/K` an extension and `L/K` finite normal. Restriction of
`Gal(Ω/F)` to `Gal(L/K)` along a `K`-embedding `j : L →ₐ[K] Ω` has open kernel: an automorphism of
`Ω/F` fixing the images under `j` of a `K`-basis of `L` fixes `j(L)`, and those images generate a
finite extension of `F`. -/
theorem _root_.AlgHom.isOpen_ker_restrictNormalHom_comp_restrictScalarsHom
    {K F L Ω : Type*} [Field K] [Field F] [Field L] [Field Ω] [Algebra K F] [Algebra K L]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower K F Ω] [Algebra.IsAlgebraic F Ω]
    [FiniteDimensional K L] [Normal K L] (j : L →ₐ[K] Ω) :
    IsOpen ((j.restrictNormalHom.comp
      (AlgEquiv.restrictScalarsHom K : Gal(Ω/F) →* Gal(Ω/K))).ker : Set Gal(Ω/F)) := by
  let b := Module.finBasis K L
  let E := IntermediateField.adjoin F (Set.range fun i ↦ j (b i))
  have : FiniteDimensional F E := IntermediateField.finiteDimensional_adjoin
    fun x _ ↦ Algebra.IsIntegral.isIntegral x
  refine Subgroup.isOpen_mono (fun τ hτ ↦ ?_) E.fixingSubgroup_isOpen
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, AlgHom.restrictNormalHom_eq_iff]
  -- `τ ∘ j` and `j` are `K`-linear maps agreeing on the basis `b`.
  have h : ((AlgEquiv.restrictScalars K τ : Ω ≃ₐ[K] Ω) : Ω →ₐ[K] Ω).toLinearMap ∘ₗ
      j.toLinearMap = j.toLinearMap :=
    b.ext fun i ↦ hτ ⟨j (b i), IntermediateField.subset_adjoin F _ ⟨i, rfl⟩⟩
  exact fun x ↦ (LinearMap.congr_fun h x).trans (by simp)

/-! ### The restriction map -/

variable (K F L : Type*) [Field K] [Field F] [Algebra K F] [Field L] [Algebra K L] [Normal K L]

variable {K F L} in
/-- Restriction of `G_F` to `Gal(L/K)` along `j : L →ₐ[K] Fᵃˡᵍ`, with source Mathlib's
`Field.absoluteGaloisGroup F`. That type carries its own group instance, which is not reducibly
the one of `Gal(Fᵃˡᵍ/F)`, so `AlgHom.restrictNormalHom_commutes` and
`AlgHom.restrictNormalHom_eq_iff` are restated below for this source; rewriting with the originals
would have to cross the two instances. -/
private def restrictAlong (j : L →ₐ[K] AlgebraicClosure F) :
    Field.absoluteGaloisGroup F →* Gal(L/K) :=
  j.restrictNormalHom.comp (AlgEquiv.restrictScalarsHom K)

variable {K F L} in
/-- `restrictAlong j τ` is the automorphism of `L` intertwined with `τ` by `j`. -/
private theorem restrictAlong_commutes (j : L →ₐ[K] AlgebraicClosure F)
    (τ : Field.absoluteGaloisGroup F) (y : L) :
    j (restrictAlong j τ y) = τ.toRingEquiv (j y) :=
  j.restrictNormalHom_commutes _ y

variable {K F L} in
/-- `restrictAlong j τ` is the unique automorphism of `L` intertwined with `τ` by `j`. -/
private theorem restrictAlong_eq_iff (j : L →ₐ[K] AlgebraicClosure F)
    {τ : Field.absoluteGaloisGroup F} {σ : Gal(L/K)} :
    restrictAlong j τ = σ ↔ ∀ y, j (σ y) = τ.toRingEquiv (j y) :=
  ⟨fun h y ↦ h ▸ restrictAlong_commutes j τ y, fun h ↦ AlgEquiv.ext fun y ↦
    j.injective ((restrictAlong_commutes j τ y).trans (h y).symm)⟩

variable {K F L} in
/-- Precomposing `j` with an automorphism `ρ` of `L/K` conjugates `restrictAlong j` by `ρ`. -/
private theorem restrictAlong_comp (j : L →ₐ[K] AlgebraicClosure F) (ρ : Gal(L/K))
    (τ : Field.absoluteGaloisGroup F) :
    restrictAlong (j.comp (ρ : L →ₐ[K] L)) τ = ρ⁻¹ * restrictAlong j τ * ρ := by
  rw [restrictAlong_eq_iff]
  intro y
  simp [AlgEquiv.mul_apply, restrictAlong_commutes]

variable {K F L} in
/-- Restriction of `G_F` to `Gal(L/K)` along `j` has open kernel. -/
private theorem isOpen_ker_restrictAlong [FiniteDimensional K L]
    (j : L →ₐ[K] AlgebraicClosure F) :
    IsOpen ((restrictAlong j).ker : Set (Field.absoluteGaloisGroup F)) :=
  AlgHom.isOpen_ker_restrictNormalHom_comp_restrictScalarsHom j

/-- **Restriction of `G_F^ab` to a finite normal layer `L/K`**, for an extension `F/K`: the class
of `τ ∈ G_F` goes to the class of the automorphism `σ` of `L/K` with `j ∘ σ = τ ∘ j`, for any
`K`-embedding `j : L →ₐ[K] Fᵃˡᵍ` (`decompositionRestrict_mk`). The value does not depend on `j`.
For a completion `F = K_v` of a number field the image of `G_F` in `Gal(L/K)` is the decomposition
group of the place of `L` above `v` given by `j`. -/
def decompositionRestrict [FiniteDimensional K L] :
    Field.absoluteGaloisGroupAbelianization F →* Abelianization Gal(L/K) :=
  -- With the discrete topology on `Gal(L/K)^ab`, the restriction is continuous because its
  -- kernel is open, so it factors through the topological abelianization.
  letI : TopologicalSpace (Abelianization Gal(L/K)) := ⊥
  haveI : DiscreteTopology (Abelianization Gal(L/K)) := ⟨rfl⟩
  (TopologicalAbelianization.lift
    ⟨Abelianization.of.comp (restrictAlong IsAlgClosed.lift),
      (Abelianization.of.comp (restrictAlong IsAlgClosed.lift)).continuous_of_isOpen_ker
        (Subgroup.isOpen_mono (fun τ hτ ↦ by
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hτ, map_one])
          (isOpen_ker_restrictAlong IsAlgClosed.lift))⟩).toMonoidHom

variable {K F L} in
/-- `decompositionRestrict` on the class of `τ`, along the embedding used to define it. -/
private theorem decompositionRestrict_mk_lift [FiniteDimensional K L]
    (τ : Field.absoluteGaloisGroup F) :
    decompositionRestrict K F L (τ : Field.absoluteGaloisGroupAbelianization F) =
      Abelianization.of (restrictAlong IsAlgClosed.lift τ) := by
  let : TopologicalSpace (Abelianization Gal(L/K)) := ⊥
  have : DiscreteTopology (Abelianization Gal(L/K)) := ⟨rfl⟩
  rw [decompositionRestrict]
  exact TopologicalAbelianization.lift_mk _ τ

variable {K F L} [FiniteDimensional K L]

/-- **The characterizing equation of `decompositionRestrict`.** For every `K`-embedding
`j : L →ₐ[K] Fᵃˡᵍ`, the class of `τ ∈ G_F` goes to the class of the automorphism `σ` of `L/K` with
`j ∘ σ = τ ∘ j`. -/
theorem decompositionRestrict_mk (j : L →ₐ[K] AlgebraicClosure F)
    (τ : Field.absoluteGaloisGroup F) (σ : Gal(L/K)) (hσ : ∀ y : L, j (σ y) = τ.toRingEquiv (j y)) :
    decompositionRestrict K F L (τ : Field.absoluteGaloisGroupAbelianization F) =
      Abelianization.of σ := by
  -- Two embeddings differ by an automorphism `ρ`, and the restrictions by conjugation by `ρ`.
  obtain ⟨ρ, rfl⟩ := (IsAlgClosed.lift : L →ₐ[K] AlgebraicClosure F).exists_comp_eq_of_normal j
  rw [← (restrictAlong_eq_iff _).2 hσ, restrictAlong_comp]
  simp [decompositionRestrict_mk_lift]

/-- `decompositionRestrict` on the class of `τ`, computed along any `K`-embedding
`j : L →ₐ[K] Fᵃˡᵍ` as the class of the restriction of `τ` to `j(L)`. -/
theorem decompositionRestrict_mk_eq_restrictNormalHom (j : L →ₐ[K] AlgebraicClosure F)
    (τ : Field.absoluteGaloisGroup F) :
    decompositionRestrict K F L (τ : Field.absoluteGaloisGroupAbelianization F) =
      Abelianization.of (j.restrictNormalHom (AlgEquiv.restrictScalarsHom K τ)) :=
  decompositionRestrict_mk j τ _ (restrictAlong_commutes j τ)

/-- **Compatibility with restriction to a normal subextension.** For a `K`-embedding
`f : M →ₐ[K] L` of a finite normal extension `M/K`, restricting `G_F^ab` to `Gal(L/K)^ab` and then
to `Gal(M/K)^ab` along `f` is restricting `G_F^ab` to `Gal(M/K)^ab`. -/
theorem decompositionRestrict_comp {M : Type*} [Field M] [Algebra K M] [FiniteDimensional K M]
    [Normal K M] (f : M →ₐ[K] L) :
    (Abelianization.map f.restrictNormalHom).comp (decompositionRestrict K F L) =
      decompositionRestrict K F M := by
  refine QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun τ ↦ ?_)
  let j : L →ₐ[K] AlgebraicClosure F := IsAlgClosed.lift
  have hσ := restrictAlong_commutes j τ
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [decompositionRestrict_mk j τ _ hσ, Abelianization.map_of,
    decompositionRestrict_mk (j.comp f) τ (f.restrictNormalHom (restrictAlong j τ)) fun y ↦ by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, f.restrictNormalHom_commutes, hσ]]

/-! ### Comparison with restriction along the separable closures -/

/-- **`decompositionRestrict` along the separable closures.** Let `iota : L →ₐ[K] Kˢ` embed `L`
in the separable closure of `K` and `τ : Kˢ →ₐ[K] Fˢ` be an embedding of separable closures. Then
the class of `σ ∈ G_F` goes to the class of the restriction to `L`, along `iota`, of the image of
`σ` under `absoluteGaloisGroupMap τ : G_F → G_K`. -/
theorem decompositionRestrict_mk_eq_restrictNormalHom_absoluteGaloisGroupMap
    (iota : L →ₐ[K] SeparableClosure K) (τ : SeparableClosure K →ₐ[K] SeparableClosure F)
    (σ : Field.absoluteGaloisGroup F) :
    decompositionRestrict K F L (σ : Field.absoluteGaloisGroupAbelianization F) =
      Abelianization.of (iota.restrictNormalHom
        (absoluteGaloisGroupMap τ (absoluteGaloisGroupRestrictEquiv F σ))) := by
  refine decompositionRestrict_mk
    ((((separableClosure F (AlgebraicClosure F)).val.restrictScalars K).comp τ).comp iota) σ _
    fun y ↦ ?_
  simp only [AlgHom.comp_apply, AlgHom.restrictNormalHom_commutes,
    absoluteGaloisGroupMap_commutes, AlgHom.restrictScalars_apply]
  exact coe_absoluteGaloisGroupRestrictEquiv_apply F σ (τ (iota y))

end TauCeti
