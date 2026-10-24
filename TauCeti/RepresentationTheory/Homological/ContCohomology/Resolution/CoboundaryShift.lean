/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Coinduced
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.GradedContraction
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Coboundary shifts of the coinduced resolution by chain endomorphisms

Let `X` be a smooth discrete representation of a compact group `G`, and let `z` and `w` be
homogeneous elements of the total coinduced resolution `X.gradedResolutionTopRep`, of degrees
`m + 1` and `m`, both fixed by `G`. If some linear functional takes the value `1` at `z`, which
over a field holds for every `z ≠ 0`, then there is an equivariant endomorphism `Φ` of the total
resolution, of degree zero, commuting with the differential `d` and fixing the augmentation,
with

```text
Φ z = z + d w.
```

So over a field a nonzero invariant cocycle can be moved, by a chain endomorphism over the identity
of `X`, to any cocycle differing from it by the differential of an invariant element. This is
useful for constructions on representing cocycles that are not additive, such as Evens'
multiplicative transfer, the class of the tensor power `z ⊗ ⋯ ⊗ z`: a construction that is
functorial in chain maps over the identity and whose classes are invariant under them
(`TopRep.ResolutionContraction.gradedCohomologyClass_map`) then depends on `z` only through its
class.

The endomorphism is `Φ = 1 + d ∘ h + h ∘ d` for an equivariant `h` of degree `-1` with `h z = w`,
so `Φ` is homotopic to the identity; what matters is the exact equation `Φ z = z + d w`, not only
the equality of classes. Such an `h` exists because the degree-`m` term `C(G, Y)` of the resolution
is coinduced: by Frobenius reciprocity (`ContRepresentation.coind₁Lift`), the linear map
`v ↦ f v • w 1` into `Y` lifts to the equivariant map `v ↦ (x ↦ f (x⁻¹ • v) • x • w 1)` into
`C(G, Y)`, which sends the invariant vector `z` with `f z = 1` to the invariant element
`x ↦ x • w 1 = w x`.

## Main results

* `TopRep.exists_gradedResolutionTopRep_hom_apply_eq_add_of_apply_eq_one`: a chain
  endomorphism over the identity with `Φ z = z + d w`, for `z` with a functional equal to `1` at
  `z`.
* `TopRep.exists_gradedResolutionTopRep_hom_apply_eq_add`: the same over a field, for every
  `z ≠ 0`.

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

variable (hX : TauCeti.IsSmoothDiscrete R X) (m : ℕ) (f : X.gradedResolutionModule →ₗ[R] R)
  (c : (resolutionX X m).V)

/-- The equivariant map from the degree `m + 1` term to the degree `m` term of the total
resolution lifting `v ↦ f v • c` to the coinduced representation. -/
private noncomputable def shiftComponent : resolutionX X (m + 1 + 1) ⟶ resolutionX X (m + 1) :=
  ofHom (ContRepresentation.coind₁Lift
    ((f ∘ₗ DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) (m + 1)).smulRight c)
    ((hX.resolutionX (m + 1 + 1)).continuous_conj (hX.resolutionX m) _))

private theorem shiftComponent_apply_apply (v : (resolutionX X (m + 1 + 1)).V) (x : G) :
    (shiftComponent hX m f c).hom v x =
      f (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) (m + 1)
        ((resolutionX X (m + 1 + 1)).ρ x⁻¹ v)) • (resolutionX X m).ρ x c := by
  simp [shiftComponent]

/-- The degree `-1` map of the total resolution that applies `shiftComponent` to the
degree `m + 1` component and vanishes on the others. -/
private noncomputable def shiftHomotopyLinear :
    X.gradedResolutionModule →ₗ[R] X.gradedResolutionModule :=
  DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) m ∘ₗ
    (shiftComponent hX m f c).hom.toLinearMap ∘ₗ
      DirectSum.component R ℕ (fun n ↦ (resolutionX X (n + 1)).V) (m + 1)

private theorem shiftHomotopyLinear_lof_self (v : (resolutionX X (m + 1 + 1)).V) :
    shiftHomotopyLinear hX m f c
        (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) (m + 1) v) =
      DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) m
        ((shiftComponent hX m f c).hom v) := by
  simp only [shiftHomotopyLinear, LinearMap.comp_apply, DirectSum.component.lof_self]
  rfl

private theorem shiftHomotopyLinear_lof_of_ne {n : ℕ} (hn : n ≠ m + 1)
    (v : (resolutionX X (n + 1)).V) :
    shiftHomotopyLinear hX m f c
      (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n v) = 0 := by
  have h : DirectSum.component R ℕ (fun n ↦ (resolutionX X (n + 1)).V) (m + 1)
      (DirectSum.lof R ℕ (fun n ↦ (resolutionX X (n + 1)).V) n v) = 0 := by
    rw [DirectSum.lof_eq_of, ← DirectSum.apply_eq_component]
    exact DirectSum.of_eq_of_ne (β := fun n ↦ (resolutionX X (n + 1)).V) n (m + 1) v (Ne.symm hn)
  simp only [shiftHomotopyLinear, LinearMap.comp_apply, h, map_zero]

private theorem shiftHomotopyLinear_eq_zero_of_mem {p : ℤ} (hp : p ≠ ((m + 1 : ℕ) : ℤ))
    {v : X.gradedResolutionModule} (hv : v ∈ X.gradedResolutionPiece p) :
    shiftHomotopyLinear hX m f c v = 0 := by
  rcases lt_or_ge p 0 with hp0 | hp0
  · rw [X.gradedResolutionPiece_of_neg hp0, Submodule.mem_bot] at hv
    rw [hv, map_zero]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp0
    rw [gradedResolutionPiece_natCast] at hv
    obtain ⟨y, rfl⟩ := hv
    exact shiftHomotopyLinear_lof_of_ne hX m f c (fun h ↦ hp (congrArg _ h)) y

private theorem isHomogeneous_shiftHomotopyLinear :
    TauCeti.LinearMap.IsHomogeneous (shiftHomotopyLinear hX m f c) X.gradedResolutionPiece
      X.gradedResolutionPiece (-1) := by
  refine TauCeti.LinearMap.isHomogeneous_def.2 fun p v hv ↦ ?_
  by_cases hp : p = ((m + 1 : ℕ) : ℤ)
  · subst hp
    rw [gradedResolutionPiece_natCast] at hv
    obtain ⟨y, rfl⟩ := hv
    rw [shiftHomotopyLinear_lof_self, show ((m + 1 : ℕ) : ℤ) + -1 = (m : ℤ) by push_cast; ring]
    exact X.lof_mem_gradedResolutionPiece m _
  · rw [shiftHomotopyLinear_eq_zero_of_mem hX m f c hp hv]
    exact zero_mem _

private theorem shiftHomotopyLinear_equivariant (g : G) (v : X.gradedResolutionModule) :
    shiftHomotopyLinear hX m f c (X.gradedResolutionRepresentation g v) =
      X.gradedResolutionRepresentation g (shiftHomotopyLinear hX m f c v) := by
  simp only [shiftHomotopyLinear, LinearMap.comp_apply]
  rw [gradedResolutionRepresentation_lof, component_gradedResolutionRepresentation]
  exact congrArg _ (hom_comm_apply (shiftComponent hX m f c) g _)

variable [DiscreteTopology R]

/-- `shiftHomotopyLinear` as an endomorphism of the discrete total resolution. -/
private noncomputable def shiftHomotopy : X.gradedResolutionTopRep ⟶ X.gradedResolutionTopRep :=
  (TauCeti.discreteTopRepFunctor R G).map <| Rep.ofHom <|
    (shiftHomotopyLinear hX m f c).intertwiningMap_of_isIntertwiningMap
      X.gradedResolutionRepresentation X.gradedResolutionRepresentation
      (shiftHomotopyLinear_equivariant hX m f c)

/-- The chain endomorphism `1 + d ∘ h + h ∘ d` of the total resolution, for `h = shiftHomotopy`. -/
private noncomputable def shift : X.gradedResolutionTopRep ⟶ X.gradedResolutionTopRep :=
  𝟙 _ + shiftHomotopy hX m f c ≫ X.gradedResolutionTopRepDifferential +
    X.gradedResolutionTopRepDifferential ≫ shiftHomotopy hX m f c

private theorem shift_hom_apply (v : X.gradedResolutionModule) :
    (shift hX m f c).hom v = v + X.gradedResolutionDifferential (shiftHomotopyLinear hX m f c v) +
      shiftHomotopyLinear hX m f c (X.gradedResolutionDifferential v) := by
  rw [← gradedResolutionTopRepDifferential_apply, ← gradedResolutionTopRepDifferential_apply]
  -- The underlying map of a sum of composites of morphisms of `TopRep` is the sum of the composites
  -- of the underlying maps by definition (`TopRep.hom_add`, `TopRep.hom_comp`), and that of
  -- `shiftHomotopy` is `shiftHomotopyLinear` (`TauCeti.discreteTopRepFunctor_map_apply`).
  rfl

end Homotopy

variable [DiscreteTopology R]

/-- **Realizing a coboundary shift by a chain endomorphism.** Let `z` and `w` be homogeneous
elements of degrees `m + 1` and `m` of the total coinduced resolution of a smooth discrete
representation `X` of a compact group, both fixed by `G`, and let `f` be a linear functional with
`f z = 1`. Then some endomorphism `Φ` of the total resolution commutes with the differential, fixes
the augmentation, has degree zero, and satisfies `Φ z = z + d w`. -/
theorem exists_gradedResolutionTopRep_hom_apply_eq_add_of_apply_eq_one
    (hX : TauCeti.IsSmoothDiscrete R X) {m : ℕ}
    {z w : X.gradedResolutionModule} (hz : z ∈ X.gradedResolutionPiece ((m + 1 : ℕ) : ℤ))
    (hzinv : ∀ g, X.gradedResolutionTopRep.ρ g z = z) (hw : w ∈ X.gradedResolutionPiece m)
    (hwinv : ∀ g, X.gradedResolutionTopRep.ρ g w = w) (f : X.gradedResolutionModule →ₗ[R] R)
    (hf : f z = 1) :
    ∃ Φ : X.gradedResolutionTopRep ⟶ X.gradedResolutionTopRep,
      X.gradedResolutionTopRepDifferential ≫ Φ = Φ ≫ X.gradedResolutionTopRepDifferential ∧
      (∀ x, Φ.hom (X.gradedResolutionAugmentation x) = X.gradedResolutionAugmentation x) ∧
      TauCeti.LinearMap.IsHomogeneous Φ.hom.toLinearMap X.gradedResolutionPiece
        X.gradedResolutionPiece 0 ∧
      Φ.hom z = z + X.gradedResolutionDifferential w := by
  rw [gradedResolutionPiece_natCast] at hz hw
  obtain ⟨z₀, rfl⟩ := hz
  obtain ⟨w₀, rfl⟩ := hw
  let c : (resolutionX X m).V := (w₀ : C(G, (resolutionX X m).V)) 1
  have hD := X.isHomogeneous_gradedResolutionDifferential
  have hh := isHomogeneous_shiftHomotopyLinear hX m f c
  refine ⟨shift hX m f c, ?_, fun x ↦ ?_, ?_, ?_⟩
  · have key (v : X.gradedResolutionModule) :
        (shift hX m f c).hom (X.gradedResolutionTopRepDifferential.hom v) =
          X.gradedResolutionTopRepDifferential.hom ((shift hX m f c).hom v) := by
      simp only [gradedResolutionTopRepDifferential_apply, shift_hom_apply, map_add,
        gradedResolutionDifferential_sq, map_zero, add_zero]
      -- The two sides agree up to the identification of the carrier of the discrete total
      -- resolution with the direct sum, `TopRep.gradedResolutionTopRep_V`.
      rfl
    ext v
    exact key v
  · rw [shift_hom_apply, gradedResolutionDifferential_augmentation, map_zero, add_zero,
      shiftHomotopyLinear_eq_zero_of_mem hX m f c (by push_cast; omega)
        (X.gradedResolutionAugmentation_mem x), map_zero, add_zero]
  · refine TauCeti.LinearMap.isHomogeneous_def.2 fun p v hv ↦ ?_
    have h₁ := hD.map_mem (hh.map_mem hv)
    have h₂ := hh.map_mem (hD.map_mem hv)
    rw [neg_add_cancel_right] at h₁
    rw [add_neg_cancel_right] at h₂
    rw [add_zero]
    convert add_mem (add_mem hv h₁) h₂ using 1
    exact shift_hom_apply hX m f c v
  · -- `z₀` and `w₀` are invariant, since the inclusions of the terms are injective.
    have hz₀ (g : G) : (resolutionX X (m + 1 + 1)).ρ g z₀ = z₀ := by
      have h := hzinv g
      rw [gradedResolutionTopRep_ρ_lof] at h
      exact DirectSum.of_injective (β := fun n ↦ (resolutionX X (n + 1)).V) (m + 1) h
    have hw₀ (g : G) : (resolutionX X (m + 1)).ρ g w₀ = w₀ := by
      have h := hwinv g
      rw [gradedResolutionTopRep_ρ_lof] at h
      exact DirectSum.of_injective (β := fun n ↦ (resolutionX X (n + 1)).V) m h
    -- `h z = w`: the lift of `v ↦ f v • w 1` takes `z₀` to `x ↦ x • w₀ 1 = w₀ x`.
    have hhz : (shiftComponent hX m f c).hom z₀ = w₀ := by
      ext x : 1
      rw [shiftComponent_apply_apply, hz₀, hf, one_smul]
      have h := congrArg (fun F : (resolutionX X (m + 1)).V ↦ F x) (hw₀ x)
      rw [ContRepresentation.coind₁_apply_apply, inv_mul_cancel] at h
      exact h
    -- `h (d z) = 0`, since `d z` lies in degree `m + 2`.
    rw [shift_hom_apply, shiftHomotopyLinear_lof_self, hhz,
      gradedResolutionDifferential_lof X (m + 1) z₀,
      shiftHomotopyLinear_lof_of_ne hX m f c (by omega), add_zero]

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
  exists_gradedResolutionTopRep_hom_apply_eq_add_of_apply_eq_one hX hz hzinv hw hwinv f hf

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

end TopRep
