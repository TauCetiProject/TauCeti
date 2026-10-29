/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Coinduced
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.GradedContraction
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Ideal.Int

/-!
# Coboundary shifts of the coinduced resolution by chain endomorphisms

Let `X` be a smooth discrete representation of a compact group `G`, and let `z` and `w` be
homogeneous elements of the total coinduced resolution `X.gradedResolutionTopRep`, of degrees
`m + 1` and `m`, both fixed by `G`. If linear maps from the total resolution to its degree `m`
term take every value at `z`, which holds for every `z ≠ 0` over a field and also, when `X` is
killed by `2`, over any commutative ring in which `2` generates a maximal ideal, such as `ℤ`, then
there is an equivariant endomorphism `Φ` of the total resolution, of degree zero, commuting with
the differential `d` and fixing the augmentation, with

```text
Φ z = z + d w.
```

So over a field, or with `𝔽₂` coefficients over `ℤ`, a nonzero invariant cocycle can be moved, by
a chain endomorphism over the identity of `X`, to any cocycle differing from it by the differential
of an invariant element. This is useful for constructions on representing cocycles that are not
additive, such as Evens' multiplicative transfer, the class of the tensor power `z ⊗ ⋯ ⊗ z`: a
construction that is functorial in chain maps over the identity and whose classes are invariant
under them (`TopRep.ResolutionContraction.gradedCohomologyClass_map`) then depends on `z` only
through its class.

The endomorphism is `Φ = 1 + d ∘ h + h ∘ d` for an equivariant `h` of degree `-1` with `h z = w`,
so `Φ` is homotopic to the identity; what matters is the exact equation `Φ z = z + d w`, not only
the equality of classes. Such an `h` exists because the degree-`m` term `C(G, Y)` of the resolution
is coinduced: by Frobenius reciprocity (`ContRepresentation.coind₁Lift`), a linear map `φ` into
`Y` with `φ z = w 1` lifts to the equivariant map `v ↦ (x ↦ x • φ (x⁻¹ • v))` into `C(G, Y)`,
which sends the invariant vector `z` to the invariant element `x ↦ x • w 1 = w x`.

## Main results

* `TopRep.exists_gradedResolutionTopRep_hom_apply_eq_add_of_forall_exists_apply_eq`: a chain
  endomorphism over the identity with `Φ z = z + d w`, for `z` at which linear maps to the degree
  `m` term take every value.
* `TopRep.exists_gradedResolutionTopRep_hom_apply_eq_add`: the same over a field, for every
  `z ≠ 0`.
* `TopRep.exists_gradedResolutionTopRep_hom_apply_eq_add_of_add_self_eq_zero`: the same for every
  `z ≠ 0` when `X` is killed by `2` and `2` generates a maximal ideal of the coefficient ring.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer. Math.
  Soc. 108 (1963), §§2–5, for the multiplicative transfer computed on representing cocycles.
-/

public section

open CategoryTheory
open scoped DirectSum

namespace TopRep

universe u v w

section Ring

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {X : TopRep.{max v w} R G}

section Homotopy

variable (hX : TauCeti.IsSmoothDiscrete R X) (m : ℕ)
  (φ : X.gradedResolutionModule →ₗ[R] (resolutionX X m).V)

/-- The equivariant map from the degree `m + 1` term to the degree `m` term of the total
resolution lifting `φ` to the coinduced representation. -/
private noncomputable def shiftComponent : resolutionX X (m + 1 + 1) ⟶ resolutionX X (m + 1) :=
  ofHom (ContRepresentation.coind₁Lift
    (φ ∘ₗ DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) (m + 1))
    ((hX.resolutionX (m + 1 + 1)).continuous_conj (hX.resolutionX m) _))

private theorem shiftComponent_apply_apply (v : (resolutionX X (m + 1 + 1)).V) (x : G) :
    (shiftComponent hX m φ).hom v x =
      (resolutionX X m).ρ x (φ (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) (m + 1)
        ((resolutionX X (m + 1 + 1)).ρ x⁻¹ v))) := by
  simp [shiftComponent]

/-- The degree `-1` map of the total resolution that applies `shiftComponent` to the
degree `m + 1` component and vanishes on the others. -/
private noncomputable def shiftHomotopyLinear :
    X.gradedResolutionModule →ₗ[R] X.gradedResolutionModule :=
  DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) m ∘ₗ
    (shiftComponent hX m φ).hom.toLinearMap ∘ₗ
      DirectSum.component R ℕ (fun n ↦ (resolutionX X (n + 1)).V) (m + 1)

private theorem shiftHomotopyLinear_lof_self (v : (resolutionX X (m + 1 + 1)).V) :
    shiftHomotopyLinear hX m φ
        (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) (m + 1) v) =
      DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) m
        ((shiftComponent hX m φ).hom v) := by
  simp only [shiftHomotopyLinear, LinearMap.comp_apply, DirectSum.component.lof_self,
    ContinuousLinearMap.coe_coe, ContIntertwiningMap.toContinuousLinearMap_apply]

private theorem shiftHomotopyLinear_lof_of_ne {n : ℕ} (hn : n ≠ m + 1)
    (v : (resolutionX X (n + 1)).V) :
    shiftHomotopyLinear hX m φ
      (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n v) = 0 := by
  have h : DirectSum.component R ℕ (fun n ↦ (resolutionX X (n + 1)).V) (m + 1)
      (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n v) = 0 := by
    rw [DirectSum.lof_eq_of, ← DirectSum.apply_eq_component]
    exact DirectSum.of_eq_of_ne (β := fun n ↦ (resolutionX X (n + 1)).V) n (m + 1) v (Ne.symm hn)
  simp only [shiftHomotopyLinear, LinearMap.comp_apply, h, map_zero]

private theorem shiftHomotopyLinear_eq_zero_of_mem {p : ℤ} (hp : p ≠ ((m + 1 : ℕ) : ℤ))
    {v : X.gradedResolutionModule} (hv : v ∈ X.gradedResolutionPiece p) :
    shiftHomotopyLinear hX m φ v = 0 := by
  rcases lt_or_ge p 0 with hp0 | hp0
  · rw [X.gradedResolutionPiece_of_neg hp0, Submodule.mem_bot] at hv
    rw [hv, map_zero]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp0
    rw [gradedResolutionPiece_natCast] at hv
    obtain ⟨y, rfl⟩ := hv
    exact shiftHomotopyLinear_lof_of_ne hX m φ (fun h ↦ hp (congrArg _ h)) y

private theorem isHomogeneous_shiftHomotopyLinear :
    TauCeti.LinearMap.IsHomogeneous (shiftHomotopyLinear hX m φ) X.gradedResolutionPiece
      X.gradedResolutionPiece (-1) := by
  refine TauCeti.LinearMap.isHomogeneous_def.2 fun p v hv ↦ ?_
  by_cases hp : p = ((m + 1 : ℕ) : ℤ)
  · subst hp
    rw [gradedResolutionPiece_natCast] at hv
    obtain ⟨y, rfl⟩ := hv
    rw [shiftHomotopyLinear_lof_self, show ((m + 1 : ℕ) : ℤ) + -1 = (m : ℤ) by push_cast; ring]
    exact X.lof_mem_gradedResolutionPiece m _
  · rw [shiftHomotopyLinear_eq_zero_of_mem hX m φ hp hv]
    exact zero_mem _

private theorem shiftHomotopyLinear_equivariant (g : G) (v : X.gradedResolutionModule) :
    shiftHomotopyLinear hX m φ (X.gradedResolutionRepresentation g v) =
      X.gradedResolutionRepresentation g (shiftHomotopyLinear hX m φ v) := by
  simp only [shiftHomotopyLinear, LinearMap.comp_apply]
  rw [gradedResolutionRepresentation_lof, component_gradedResolutionRepresentation]
  exact congrArg _ (hom_comm_apply (shiftComponent hX m φ) g _)

variable [DiscreteTopology R]

/-- `shiftHomotopyLinear` as an endomorphism of the discrete total resolution. -/
private noncomputable def shiftHomotopy : X.gradedResolutionTopRep ⟶ X.gradedResolutionTopRep :=
  (TauCeti.discreteTopRepFunctor R G).map <| Rep.ofHom <|
    (shiftHomotopyLinear hX m φ).intertwiningMap_of_isIntertwiningMap
      X.gradedResolutionRepresentation X.gradedResolutionRepresentation
      (shiftHomotopyLinear_equivariant hX m φ)

/-- The chain endomorphism `1 + d ∘ h + h ∘ d` of the total resolution, for `h = shiftHomotopy`. -/
private noncomputable def shift : X.gradedResolutionTopRep ⟶ X.gradedResolutionTopRep :=
  𝟙 _ + shiftHomotopy hX m φ ≫ X.gradedResolutionTopRepDifferential +
    X.gradedResolutionTopRepDifferential ≫ shiftHomotopy hX m φ

private theorem shift_hom_apply (v : X.gradedResolutionModule) :
    (shift hX m φ).hom v = v + X.gradedResolutionDifferential (shiftHomotopyLinear hX m φ v) +
      shiftHomotopyLinear hX m φ (X.gradedResolutionDifferential v) := by
  rw [← gradedResolutionTopRepDifferential_apply, ← gradedResolutionTopRepDifferential_apply]
  -- The underlying map of a sum of composites of morphisms of `TopRep` is the sum of the composites
  -- of the underlying maps by definition (`TopRep.hom_add`, `TopRep.hom_comp`), and that of
  -- `shiftHomotopy` is `shiftHomotopyLinear` (`TauCeti.discreteTopRepFunctor_map_apply`).
  rfl

private theorem isHomogeneous_shift :
    TauCeti.LinearMap.IsHomogeneous (shift hX m φ).hom.toLinearMap X.gradedResolutionPiece
      X.gradedResolutionPiece 0 := by
  have hD := X.isHomogeneous_gradedResolutionDifferential
  have hh := isHomogeneous_shiftHomotopyLinear hX m φ
  have h₁ := neg_add_cancel (1 : ℤ) ▸ hD.comp hh
  have h₂ := add_neg_cancel (1 : ℤ) ▸ hh.comp hD
  -- The ascription views the underlying map on the direct sum, the carrier of the discrete total
  -- resolution (`TopRep.gradedResolutionTopRep_V`).
  have e : ((shift hX m φ).hom.toLinearMap :
      X.gradedResolutionModule →ₗ[R] X.gradedResolutionModule) =
      LinearMap.id + X.gradedResolutionDifferential ∘ₗ shiftHomotopyLinear hX m φ +
        shiftHomotopyLinear hX m φ ∘ₗ X.gradedResolutionDifferential :=
    LinearMap.ext (shift_hom_apply hX m φ)
  exact e ▸ ((TauCeti.LinearMap.isHomogeneous_id _).add h₁).add h₂

end Homotopy

variable [DiscreteTopology R]

omit [CompactSpace G] in
/-- An element of a term of the resolution is invariant once its inclusion into the total
resolution is, since the inclusion is injective. -/
private theorem resolutionX_ρ_eq_of_gradedResolutionTopRep_ρ_lof_eq {n : ℕ}
    {v : (resolutionX X (n + 1)).V} {g : G}
    (h : X.gradedResolutionTopRep.ρ g (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n v) =
      DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n v) :
    (resolutionX X (n + 1)).ρ g v = v := by
  rw [gradedResolutionTopRep_ρ_lof] at h
  exact DirectSum.of_injective (β := fun n ↦ (resolutionX X (n + 1)).V) n h

/-- **Realizing a coboundary shift by a chain endomorphism.** Let `z` and `w` be homogeneous
elements of degrees `m + 1` and `m` of the total coinduced resolution of a smooth discrete
representation `X` of a compact group, both fixed by `G`, and suppose that linear maps from the
total resolution to its degree `m` term take every value at `z`; a linear functional `f` with
`f z = 1` gives `v ↦ f v • c` with value `c`. Then some endomorphism `Φ` of the total resolution
commutes with the differential, fixes the augmentation, has degree zero, and satisfies
`Φ z = z + d w`. -/
theorem exists_gradedResolutionTopRep_hom_apply_eq_add_of_forall_exists_apply_eq
    (hX : TauCeti.IsSmoothDiscrete R X) {m : ℕ}
    {z w : X.gradedResolutionModule} (hz : z ∈ X.gradedResolutionPiece ((m + 1 : ℕ) : ℤ))
    (hzinv : ∀ g, X.gradedResolutionTopRep.ρ g z = z) (hw : w ∈ X.gradedResolutionPiece m)
    (hwinv : ∀ g, X.gradedResolutionTopRep.ρ g w = w)
    (hφ : ∀ c : (resolutionX X m).V,
      ∃ φ : X.gradedResolutionModule →ₗ[R] (resolutionX X m).V, φ z = c) :
    ∃ Φ : X.gradedResolutionTopRep ⟶ X.gradedResolutionTopRep,
      X.gradedResolutionTopRepDifferential ≫ Φ = Φ ≫ X.gradedResolutionTopRepDifferential ∧
      (∀ x, Φ.hom (X.gradedResolutionAugmentation x) = X.gradedResolutionAugmentation x) ∧
      TauCeti.LinearMap.IsHomogeneous Φ.hom.toLinearMap X.gradedResolutionPiece
        X.gradedResolutionPiece 0 ∧
      Φ.hom z = z + X.gradedResolutionDifferential w := by
  rw [gradedResolutionPiece_natCast] at hz hw
  obtain ⟨z₀, rfl⟩ := hz
  obtain ⟨w₀, rfl⟩ := hw
  obtain ⟨φ, hφz⟩ := hφ ((w₀ : C(G, (resolutionX X m).V)) 1)
  refine ⟨shift hX m φ, ?_, fun x ↦ ?_, isHomogeneous_shift hX m φ, ?_⟩
  · have key (v : X.gradedResolutionModule) :
        (shift hX m φ).hom (X.gradedResolutionTopRepDifferential.hom v) =
          X.gradedResolutionTopRepDifferential.hom ((shift hX m φ).hom v) := by
      simp only [gradedResolutionTopRepDifferential_apply, shift_hom_apply, map_add,
        gradedResolutionDifferential_sq, map_zero, add_zero]
      -- The two sides agree up to the identification of the carrier of the discrete total
      -- resolution with the direct sum, `TopRep.gradedResolutionTopRep_V`.
      rfl
    ext v
    exact key v
  · rw [shift_hom_apply, gradedResolutionDifferential_augmentation, map_zero, add_zero,
      shiftHomotopyLinear_eq_zero_of_mem hX m φ (by push_cast; omega)
        (X.gradedResolutionAugmentation_mem x), map_zero, add_zero]
  · have hz₀ (g : G) : (resolutionX X (m + 1 + 1)).ρ g z₀ = z₀ :=
      resolutionX_ρ_eq_of_gradedResolutionTopRep_ρ_lof_eq (hzinv g)
    have hw₀ (g : G) : (resolutionX X (m + 1)).ρ g w₀ = w₀ :=
      resolutionX_ρ_eq_of_gradedResolutionTopRep_ρ_lof_eq (hwinv g)
    -- `h z = w`: the lift of `φ` takes `z₀` to `x ↦ x • φ z = x • w₀ 1 = w₀ x`.
    have hhz : (shiftComponent hX m φ).hom z₀ = w₀ := by
      ext x : 1
      rw [shiftComponent_apply_apply, hz₀, hφz]
      have h := congrArg (fun F : (resolutionX X (m + 1)).V ↦ F x) (hw₀ x)
      rw [ContRepresentation.coind₁_apply_apply, inv_mul_cancel] at h
      exact h
    -- `h (d z) = 0`, since `d z` lies in degree `m + 2`.
    rw [shift_hom_apply, shiftHomotopyLinear_lof_self, hhz,
      gradedResolutionDifferential_lof X (m + 1) z₀,
      shiftHomotopyLinear_lof_of_ne hX m φ (by omega), add_zero]

end Ring

section Field

variable {R : Type u} [Field R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {X : TopRep.{max v w} R G}

/-- **Realizing a coboundary shift by a chain endomorphism, over a field.** Let `z ≠ 0` and `w` be
homogeneous elements of degrees `m + 1` and `m` of the total coinduced resolution of a smooth
discrete representation `X` of a compact group, both fixed by `G`. Then some endomorphism `Φ` of
the total resolution commutes with the differential, fixes the augmentation, has degree zero, and
satisfies `Φ z = z + d w`. -/
theorem exists_gradedResolutionTopRep_hom_apply_eq_add (hX : TauCeti.IsSmoothDiscrete R X)
    {m : ℕ} {z w : X.gradedResolutionModule} (hz : z ∈ X.gradedResolutionPiece ((m + 1 : ℕ) : ℤ))
    (hzinv : ∀ g, X.gradedResolutionTopRep.ρ g z = z) (hz0 : z ≠ 0)
    (hw : w ∈ X.gradedResolutionPiece m) (hwinv : ∀ g, X.gradedResolutionTopRep.ρ g w = w) :
    ∃ Φ : X.gradedResolutionTopRep ⟶ X.gradedResolutionTopRep,
      X.gradedResolutionTopRepDifferential ≫ Φ = Φ ≫ X.gradedResolutionTopRepDifferential ∧
      (∀ x, Φ.hom (X.gradedResolutionAugmentation x) = X.gradedResolutionAugmentation x) ∧
      TauCeti.LinearMap.IsHomogeneous Φ.hom.toLinearMap X.gradedResolutionPiece
        X.gradedResolutionPiece 0 ∧
      Φ.hom z = z + X.gradedResolutionDifferential w :=
  have ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one R hz0
  exists_gradedResolutionTopRep_hom_apply_eq_add_of_forall_exists_apply_eq hX hz hzinv hw hwinv
    fun c ↦ ⟨f.smulRight c, by rw [LinearMap.smulRight_apply, hf, one_smul]⟩

/-- The endomorphism of `exists_gradedResolutionTopRep_hom_apply_eq_add` meets the hypotheses of
`TopRep.ResolutionContraction.gradedCohomologyClass_map`: for the contraction of the total
resolution by evaluation at `1`, the class of `Φ z = z + d w` is the class of `z`. -/
example [LocallyCompactSpace G] (hX : TauCeti.IsSmoothDiscrete R X) {m : ℕ}
    {z w : X.gradedResolutionModule} (hz : z ∈ X.gradedResolutionPiece ((m + 1 : ℕ) : ℤ))
    (hzinv : ∀ g, X.gradedResolutionTopRep.ρ g z = z) (hz0 : z ≠ 0)
    (hdz : X.gradedResolutionTopRepDifferential.hom z = 0)
    (hw : w ∈ X.gradedResolutionPiece m) (hwinv : ∀ g, X.gradedResolutionTopRep.ρ g w = w) :
    ∃ Φ : X.gradedResolutionTopRep ⟶ X.gradedResolutionTopRep,
      Φ.hom z = z + X.gradedResolutionDifferential w ∧
      ∀ hΦz hΦinv hΦdz, (gradedResolutionContraction hX).gradedCohomologyClass (Φ.hom z) hΦz
          hΦinv hΦdz = (gradedResolutionContraction hX).gradedCohomologyClass z hz hzinv hdz := by
  obtain ⟨Φ, hΦd, hΦι, hΦ, hΦz⟩ :=
    exists_gradedResolutionTopRep_hom_apply_eq_add hX hz hzinv hz0 hw hwinv
  refine ⟨Φ, hΦz, fun _ _ _ ↦ ?_⟩
  exact (gradedResolutionContraction hX).gradedCohomologyClass_map (gradedResolutionContraction hX)
    Φ hΦ hΦd (fun x ↦ by rw [gradedResolutionContraction_ι_apply]; exact hΦι x) hz hzinv hdz

end Field

section CharTwo

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  [(Ideal.span {(2 : R)}).IsMaximal]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {X : TopRep.{max v w} R G}

/-- **Realizing a coboundary shift by a chain endomorphism, in characteristic two.** Let `R` be a
commutative ring in which `2` generates a maximal ideal, such as `ℤ` or a field of characteristic
two, and let `X` be a smooth discrete representation of a compact group over `R` whose elements are
their own additive inverses, such as trivial `𝔽₂` coefficients over `ℤ`. Let `z ≠ 0` and `w` be
homogeneous elements of degrees `m + 1` and `m` of its total coinduced resolution, both fixed by
`G`. Then some endomorphism `Φ` of the total resolution commutes with the differential, fixes the
augmentation, has degree zero, and satisfies `Φ z = z + d w`. -/
theorem exists_gradedResolutionTopRep_hom_apply_eq_add_of_add_self_eq_zero
    (hX : TauCeti.IsSmoothDiscrete R X) (hX₂ : ∀ x : X.V, x + x = 0) {m : ℕ}
    {z w : X.gradedResolutionModule} (hz : z ∈ X.gradedResolutionPiece ((m + 1 : ℕ) : ℤ))
    (hzinv : ∀ g, X.gradedResolutionTopRep.ρ g z = z) (hz0 : z ≠ 0)
    (hw : w ∈ X.gradedResolutionPiece m) (hwinv : ∀ g, X.gradedResolutionTopRep.ρ g w = w) :
    ∃ Φ : X.gradedResolutionTopRep ⟶ X.gradedResolutionTopRep,
      X.gradedResolutionTopRepDifferential ≫ Φ = Φ ≫ X.gradedResolutionTopRepDifferential ∧
      (∀ x, Φ.hom (X.gradedResolutionAugmentation x) = X.gradedResolutionAugmentation x) ∧
      TauCeti.LinearMap.IsHomogeneous Φ.hom.toLinearMap X.gradedResolutionPiece
        X.gradedResolutionPiece 0 ∧
      Φ.hom z = z + X.gradedResolutionDifferential w := by
  refine exists_gradedResolutionTopRep_hom_apply_eq_add_of_forall_exists_apply_eq hX hz hzinv hw
    hwinv fun c ↦ ?_
  -- Both modules are killed by `2`, so they are vector spaces over the field `R ⧸ (2)`, where a
  -- nonzero vector has a functional equal to `1`.
  have hM : Module.IsTorsionBySet R X.gradedResolutionModule (Ideal.span {(2 : R)}) :=
    (Module.isTorsionBySet_span_singleton_iff 2).2 fun x ↦ by
      rw [two_smul]; exact X.gradedResolutionModule_add_self_eq_zero hX₂ x
  have hY : Module.IsTorsionBySet R (resolutionX X m).V (Ideal.span {(2 : R)}) :=
    (Module.isTorsionBySet_span_singleton_iff 2).2 fun x ↦ by
      rw [two_smul]; exact resolutionX_add_self_eq_zero X hX₂ m x
  let := Ideal.Quotient.field (Ideal.span {(2 : R)})
  let := hM.module
  let := hY.module
  have := hM.isScalarTower (S := R)
  have := hY.isScalarTower (S := R)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (R ⧸ Ideal.span {(2 : R)}) hz0
  exact ⟨(f.smulRight c).restrictScalars R, by
    rw [LinearMap.restrictScalars_apply, LinearMap.smulRight_apply, hf, one_smul]⟩

/-- The hypothesis on the coefficient ring holds for `ℤ`, the coefficient ring of trivial `𝔽₂`
coefficients `TauCeti.trivialF2`. -/
example : (Ideal.span {(2 : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 2

end CharTwo

end TopRep
