/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Algebra.PontryaginDual

/-!
# Annihilators for bilinear character pairings

For an additive subgroup `U` and a bilinear map `B`, the character annihilator consists of the
frequencies `w` at which `ψ (B u w) = 1` for all `u ∈ U`. Unlike orthogonality for a bilinear
form, this condition generally defines only an additive subgroup, not a submodule.

For a jointly continuous pairing, the restricted phase on a compact subgroup is locally
constant in the frequency. This uses Mathlib's discreteness of the Pontryagin dual of a compact
monoid, and in particular gives openness of the annihilator.
-/

public section

namespace AddSubgroup

variable {R V W W' : Type*} [CommSemiring R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- The additive subgroup of `W` pairing trivially with `U` under the character `ψ` and
bilinear map `B`. -/
noncomputable def characterAnnihilator (U : AddSubgroup V) (ψ : AddChar R Circle)
    (B : V →ₗ[R] W →ₗ[R] R) : AddSubgroup W :=
  ⨅ u : U, (ψ.toAddMonoidHom.comp (B u).toAddMonoidHom).ker

/-- A frequency is in the character annihilator precisely when its phase on `U` is trivial. -/
theorem mem_characterAnnihilator {U : AddSubgroup V} {ψ : AddChar R Circle}
    {B : V →ₗ[R] W →ₗ[R] R} {w : W} :
    w ∈ U.characterAnnihilator ψ B ↔ ∀ u ∈ U, ψ (B u w) = 1 := by
  simp [characterAnnihilator, Subtype.forall]

/-- The zero subgroup is annihilated by all frequencies. -/
@[simp] theorem characterAnnihilator_bot (ψ : AddChar R Circle) (B : V →ₗ[R] W →ₗ[R] R) :
    (⊥ : AddSubgroup V).characterAnnihilator ψ B = ⊤ := by
  ext w
  simp [mem_characterAnnihilator]

/-- The zero pairing has trivial phase at all frequencies. -/
@[simp] theorem characterAnnihilator_zero (U : AddSubgroup V) (ψ : AddChar R Circle) :
    U.characterAnnihilator ψ (0 : V →ₗ[R] W →ₗ[R] R) = ⊤ := by
  ext w
  simp [mem_characterAnnihilator]

/-- A trivial character imposes no restriction on frequencies. -/
@[simp] theorem characterAnnihilator_one (U : AddSubgroup V) (B : V →ₗ[R] W →ₗ[R] R) :
    U.characterAnnihilator 1 B = ⊤ := by
  ext w
  simp [mem_characterAnnihilator]

/-- Enlarging the subgroup shrinks its character annihilator. -/
theorem characterAnnihilator_anti (ψ : AddChar R Circle) (B : V →ₗ[R] W →ₗ[R] R) :
    Antitone (fun U : AddSubgroup V ↦ U.characterAnnihilator ψ B) :=
  fun _ _ h _ hw ↦ mem_characterAnnihilator.mpr fun u hu ↦ mem_characterAnnihilator.mp hw u (h hu)

/-- Pulling back the frequency variable of the pairing pulls back the annihilator. -/
@[simp] theorem characterAnnihilator_compl₂ [AddCommGroup W'] [Module R W']
    (U : AddSubgroup V) (ψ : AddChar R Circle) (B : V →ₗ[R] W →ₗ[R] R) (T : W' →ₗ[R] W) :
    U.characterAnnihilator ψ (B.compl₂ T) =
      (U.characterAnnihilator ψ B).comap T.toAddMonoidHom := by
  ext w
  simp [mem_characterAnnihilator, LinearMap.compl₂_apply]

/-- To annihilate a cyclic additive subgroup it suffices to annihilate its generator. -/
@[simp] theorem mem_characterAnnihilator_zmultiples {ψ : AddChar R Circle}
    {B : V →ₗ[R] W →ₗ[R] R} {v : V} {w : W} :
    w ∈ (zmultiples v).characterAnnihilator ψ B ↔ ψ (B v w) = 1 := by
  rw [mem_characterAnnihilator]
  let φ := ψ.toAddMonoidHom.comp (B.flip w).toAddMonoidHom
  exact (zmultiples_le (H := φ.ker))

/-- The character annihilator is closed when the phase is continuous in the frequency
variable for each element of the subgroup. -/
theorem isClosed_characterAnnihilator [TopologicalSpace W] (U : AddSubgroup V)
    {ψ : AddChar R Circle} {B : V →ₗ[R] W →ₗ[R] R}
    (h : ∀ u ∈ U, Continuous (fun w ↦ ψ (B u w))) :
    IsClosed (U.characterAnnihilator ψ B : Set W) := by
  have hset : (U.characterAnnihilator ψ B : Set W) = ⋂ u : U, {w | ψ (B u w) = 1} := by
    ext w
    simp [mem_characterAnnihilator, Subtype.forall]
  rw [hset]
  exact isClosed_iInter fun u ↦ isClosed_eq (h u u.property) continuous_const

/-- If the pairing is jointly continuous on `U × W` and `U` is compact, the restricted
character is locally constant as a function of the frequency. -/
theorem isLocallyConstant_characterPairing [TopologicalSpace V] [TopologicalSpace W]
    (U : AddSubgroup V) {ψ : AddChar R Circle} {B : V →ₗ[R] W →ₗ[R] R}
    (hU : IsCompact (U : Set V)) (h : Continuous (fun p : U × W ↦ ψ (B p.1 p.2))) :
    IsLocallyConstant (fun w (u : U) ↦ ψ (B u w)) := by
  let : CompactSpace U := isCompact_iff_compactSpace.mp hU
  let χ (w : W) : PontryaginDual (Multiplicative U) :=
    { toFun := fun u ↦ ψ (B u.toAdd w)
      map_one' := by simp
      map_mul' := fun u v ↦ by simp [ψ.map_add_eq_mul]
      continuous_toFun := h.comp (continuous_toAdd.prodMk continuous_const) }
  have hχ : Continuous χ := by
    apply (ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous_iff.mpr
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact h.comp ((continuous_toAdd.comp continuous_snd).prodMk continuous_fst)
  exact (IsLocallyConstant.of_discrete (fun (η : PontryaginDual (Multiplicative U)) (u : U) ↦
    η (Multiplicative.ofAdd u))).comp_continuous hχ

/-- A compact additive subgroup has open character annihilator for a jointly continuous
pairing. No compatibility of the frequency topology with addition is needed. -/
theorem isOpen_characterAnnihilator [TopologicalSpace V] [TopologicalSpace W]
    (U : AddSubgroup V) {ψ : AddChar R Circle} {B : V →ₗ[R] W →ₗ[R] R}
    (hU : IsCompact (U : Set V)) (h : Continuous (fun p : U × W ↦ ψ (B p.1 p.2))) :
    IsOpen (U.characterAnnihilator ψ B : Set W) := by
  have hset : (U.characterAnnihilator ψ B : Set W) = {w | (fun u : U ↦ ψ (B u w)) = 1} := by
    ext w
    simp [mem_characterAnnihilator, funext_iff, Subtype.forall]
  rw [hset]
  exact (U.isLocallyConstant_characterPairing hU h).isOpen_fiber 1

end AddSubgroup
