/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Condensed.Light.LocallyConstant
public import TauCeti.Condensed.Light.Solid.Basic
public import TauCeti.Topology.Category.LightProfinite.Cartesian

import TauCeti.Algebra.Group.Hom.Iterate
import TauCeti.Condensed.Light.NullSequence.Tensor

/-!
# Discrete modules are solid

The discrete light condensed module on any module `M` is solid. A null sequence parametrized
by a light profinite set `S`, with values in a discrete module, is a locally constant function
on `S × C` vanishing on `S × {∞}`, where `C` is the convergent sequence. By compactness of `S`
it vanishes on `S × {n}` for all large `n`, uniformly in `S`. So the shift is locally nilpotent
on such families, and one minus the shift is invertible with inverse given by the finite sums
`x n = b n + b (n + 1) + ⋯`.

See Rodríguez Camargo, *Notes on Solid Geometry*, Theorem 3.2.4.
-/

public section

universe u

open CategoryTheory MonoidalCategory LightCondensed Opposite Filter

namespace TauCeti

/-- A locally constant function on `S × C` vanishing on `S × {∞}` vanishes on `S × {n}` for all
large `n`, uniformly in `S`. -/
private lemma exists_forall_ge_apply_eq_zero {M : Type*} [Zero M] {S : LightProfinite.{u}}
    (f : LocallyConstant (S ⊗ liftedSequence.{u} : LightProfinite.{u}) M)
    (hf : ∀ s, f (s, sequenceInfty) = 0) :
    ∃ N, ∀ n ≥ N, ∀ s, f (s, sequencePoint n) = 0 := by
  obtain ⟨u, v, -, hv, hu, hinf, huv⟩ := generalized_tube_lemma isCompact_univ
    isCompact_singleton (f.isLocallyConstant.isOpen_fiber 0) (s := (Set.univ : Set S))
    (t := {sequenceInfty.{u}}) (by
      rintro ⟨s, c⟩ ⟨-, hc⟩
      rw [Set.mem_singleton_iff] at hc
      subst hc
      exact hf s)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (tendsto_sequencePoint_atTop.eventually (hv.mem_nhds (hinf rfl)))
  exact ⟨N, fun n hn s ↦ huv ⟨hu trivial, hN n hn⟩⟩

/-- Including the limit point in the second coordinate sends `(s, *)` to `(s, ∞)`. -/
private lemma whiskerLeft_inftyPoint_apply {S : LightProfinite.{u}}
    (p : (S ⊗ LightProfinite.of PUnit.{u + 1} : LightProfinite.{u})) :
    (S ◁ inftyPoint.{u}) p = (p.1, sequenceInfty) :=
  (LightProfinite.whiskerLeft_apply S inftyPoint p).trans
    (congrArg (Prod.mk p.1) (inftyPoint_apply _))

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R) {S : LightProfinite.{u}}

/-- A discrete section over `S ⊗ C` restricts to zero over `S ⊗ {∞}` exactly when it vanishes
at every point `(s, ∞)`. -/
private lemma mem_ker_iff_locallyConstant
    (x : ((LightCondMod.LocallyConstant.functor R).obj M).obj.obj
      (op (S ⊗ liftedSequence.{u}))) :
    x ∈ (((LightCondMod.LocallyConstant.functor R).obj M).obj.map
        (S ◁ inftyPoint.{u}).op).hom.toAddMonoidHom.ker ↔
      ∀ s, LightCondMod.LocallyConstant.sectionsEquiv M _ x (s, sequenceInfty) = 0 := by
  rw [AddMonoidHom.mem_ker, LinearMap.toAddMonoidHom_coe,
    ← (LightCondMod.LocallyConstant.sectionsEquiv M _).map_eq_zero_iff, LocallyConstant.ext_iff]
  simp only [LightCondMod.LocallyConstant.sectionsEquiv_map_apply, LocallyConstant.zero_apply,
    whiskerLeft_inftyPoint_apply]
  exact ⟨fun h s ↦ h (s, PUnit.unit), fun h y ↦ h y.1⟩

/-- Restricting a discrete section `n` times along the successor on `C` shifts its values. -/
private lemma sectionsEquiv_iterate_map_natShift (n : ℕ)
    (x : ((LightCondMod.LocallyConstant.functor R).obj M).obj.obj
      (op (S ⊗ liftedSequence.{u}))) (s : S) (c : liftedSequence.{u}) :
    LightCondMod.LocallyConstant.sectionsEquiv M _
        ((⇑(((LightCondMod.LocallyConstant.functor R).obj M).obj.map
          (S ◁ natShift.{u}).op).hom.toAddMonoidHom)^[n] x) (s, c) =
      LightCondMod.LocallyConstant.sectionsEquiv M _ x (s, (⇑natShift.{u})^[n] c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply, ← ih]
    exact LightCondMod.LocallyConstant.sectionsEquiv_map_apply M (S ◁ natShift.{u}) _ (s, c)

/-- The locally constant realization of a discrete module is solid. -/
theorem isLightSolid_locallyConstant :
    IsLightSolid R ((LightCondMod.LocallyConstant.functor R).obj M) := by
  rw [isLightSolid_iff_bijective_free]
  intro S
  let K := (((LightCondMod.LocallyConstant.functor R).obj M).obj.map
    (S ◁ inftyPoint.{u}).op).hom.toAddMonoidHom.ker
  let T := (((LightCondMod.LocallyConstant.functor R).obj M).obj.map
    (S ◁ natShift.{u}).op).hom.toAddMonoidHom
  have hT : Set.MapsTo T K K := fun x hx ↦ by
    rw [SetLike.mem_coe, mem_ker_iff_locallyConstant] at hx ⊢
    intro s
    have h := sectionsEquiv_iterate_map_natShift M 1 x s sequenceInfty
    rwa [Function.iterate_one, iterate_natShift_apply_infty, hx s] at h
  have hnil (x) (hx : x ∈ K) : ∃ N, T^[N] x = 0 := by
    rw [mem_ker_iff_locallyConstant] at hx
    obtain ⟨N, hN⟩ := exists_forall_ge_apply_eq_zero _ hx
    refine ⟨N, (LightCondMod.LocallyConstant.sectionsEquiv M _).injective ?_⟩
    ext p
    rw [map_zero, LocallyConstant.zero_apply]
    refine (sectionsEquiv_iterate_map_natShift M N x p.1 p.2).trans ?_
    induction p.2 using liftedSequence_cases with
    | hpoint m => simpa using hN (m + N) (Nat.le_add_left N m) p.1
    | hinfty => simpa using hx p.1
  have hbij := T.bijOn_sub_of_exists_iterate_eq_zero hT hnil
  let e := nullSeqTensorFreeHomEquiv R S ((LightCondMod.LocallyConstant.functor R).obj M)
  -- The restriction `hbij.mapsTo.restrict` of `1 - T` to `K`, spelled out so its values simplify.
  let r : K → K := fun x ↦ ⟨x - T x, hbij.mapsTo x.property⟩
  have h : (fun g ↦ g - nullShift R ▷ _ ≫ g) = e.symm ∘ r ∘ e := by
    funext g
    apply e.injective
    ext
    simp only [Function.comp_apply, AddEquiv.apply_symm_apply, r, map_sub, AddSubgroup.coe_sub,
      nullSeqTensorFreeHomEquiv_nullShift_val, e, T, LinearMap.toAddMonoidHom_coe]
  rw [h]
  have hr : Function.Bijective r := hbij.bijective
  exact (e.symm.bijective.comp hr).comp e.bijective

/-- The discrete light condensed module on any module is solid. -/
theorem isLightSolid_discrete :
    IsLightSolid R ((discrete (ModuleCat.{u} R)).obj M) :=
  (IsLightSolid R).prop_of_iso ((LightCondMod.LocallyConstant.functorIsoDiscrete R).app M)
    (isLightSolid_locallyConstant M)

end TauCeti
