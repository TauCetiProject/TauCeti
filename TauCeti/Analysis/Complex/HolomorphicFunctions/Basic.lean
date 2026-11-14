/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Holomorphic functions with the compact-open topology

`holomorphicFunctions U` is the complex subalgebra of `C(U, ℂ)` consisting of holomorphic
functions on the open set `U`. Holomorphy can be checked on any ambient representative;
in particular, extension by zero outside `U` gives the same condition. The topology and
uniformity are inherited from continuous maps, so convergence means locally uniform
convergence. This subalgebra is closed and complete, and both restriction to a smaller open
set and postcomposition along a holomorphic map into another open set are continuous algebra
homomorphisms.

These algebras provide domains for continuous holomorphic functional calculi without
choosing a supremum norm on a possibly noncompact open set.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.

The closedness argument uses Mathlib's `TendstoLocallyUniformlyOn.differentiableOn`.
-/

public section

namespace TauCeti

open Filter Set Topology TopologicalSpace

/-- The algebra of holomorphic functions on an open subset of the complex plane, with the
topology inherited from `C(U, ℂ)`. -/
def holomorphicFunctions (U : Opens ℂ) : Subalgebra ℂ C(U, ℂ) where
  carrier := {f | ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z : U, g z = f z}
  zero_mem' := ⟨0, differentiableOn_const _, fun _ => rfl⟩
  one_mem' := ⟨1, differentiableOn_const _, fun _ => rfl⟩
  add_mem' := by
    rintro f h ⟨g, hg, hgf⟩ ⟨k, hk, hkh⟩
    exact ⟨g + k, hg.add hk, fun z => by simp [hgf, hkh]⟩
  mul_mem' := by
    rintro f h ⟨g, hg, hgf⟩ ⟨k, hk, hkh⟩
    exact ⟨g * k, hg.mul hk, fun z => by simp [hgf, hkh]⟩
  algebraMap_mem' c := ⟨fun _ => c, differentiableOn_const _, fun _ => rfl⟩

/-- The algebra operations are continuous in the compact-open topology. -/
instance (U : Opens ℂ) : IsTopologicalRing (holomorphicFunctions U) := by
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  exact (holomorphicFunctions U).toSubring.instIsTopologicalRing

/-- Membership is equivalent to having an ambient holomorphic representative. -/
theorem mem_holomorphicFunctions_iff {U : Opens ℂ} {f : C(U, ℂ)} :
    f ∈ holomorphicFunctions U ↔
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z : U, g z = f z := Iff.rfl

/-- Holomorphy on an open set is independent of all values outside that set. -/
theorem mem_holomorphicFunctions_iff_of_eqOn {U : Opens ℂ} {f : C(U, ℂ)}
    {g : ℂ → ℂ} (hgf : ∀ z : U, g z = f z) :
    f ∈ holomorphicFunctions U ↔ DifferentiableOn ℂ g U := by
  constructor
  · rintro ⟨k, hk, hkf⟩
    exact hk.congr fun z hz => (hgf ⟨z, hz⟩).trans (hkf ⟨z, hz⟩).symm
  · exact fun hg => ⟨g, hg, hgf⟩

/-- Equivalently, the extension by zero is holomorphic on the domain. -/
theorem mem_holomorphicFunctions_iff_extend {U : Opens ℂ} {f : C(U, ℂ)} :
    f ∈ holomorphicFunctions U ↔
      DifferentiableOn ℂ (Function.extend Subtype.val f (fun _ => 0)) U :=
  mem_holomorphicFunctions_iff_of_eqOn fun z =>
    Subtype.val_injective.extend_apply f (fun _ => 0) z

namespace HolomorphicFunctions

variable {U V W : Opens ℂ}

/-- Restrict an ambient holomorphic function to its open domain. -/
def of (U : Opens ℂ) (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g U) :
    holomorphicFunctions U :=
  ⟨⟨fun z => g z, hg.continuousOn.domRestrict⟩, g, hg, fun _ => rfl⟩

@[simp]
theorem of_apply (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g U) (z : U) :
    (of U g hg).val z = g z := (rfl)

/-- The ambient representative obtained by extending by zero. -/
noncomputable def extend (f : holomorphicFunctions U) : ℂ → ℂ :=
  Function.extend Subtype.val f.val (fun _ => 0)

@[simp]
theorem extend_apply (f : holomorphicFunctions U) (z : U) : extend f z = f.val z :=
  Subtype.val_injective.extend_apply _ _ _

/-- The zero extension vanishes outside its original domain. -/
@[simp]
theorem extend_apply_of_not_mem (f : holomorphicFunctions U) {z : ℂ} (hz : z ∉ U) :
    extend f z = 0 := by
  rw [extend, Function.extend_apply']
  rintro ⟨w, rfl⟩
  exact hz w.property

/-- Extension by zero remains holomorphic on the original open domain. -/
theorem differentiableOn_extend (f : holomorphicFunctions U) :
    DifferentiableOn ℂ (extend f) U :=
  mem_holomorphicFunctions_iff_extend.mp f.property

/-- Extension by zero is analytic near every subset of the original open domain. -/
theorem analyticOnNhd_extend {s : Set ℂ} (hs : s ⊆ U) (f : holomorphicFunctions U) :
    AnalyticOnNhd ℂ (extend f) s :=
  ((differentiableOn_extend f).analyticOnNhd U.isOpen).mono hs

/-- Recovering a holomorphic function from its zero extension does not change it. -/
@[simp]
theorem of_extend (f : holomorphicFunctions U) :
    of U (extend f) (differentiableOn_extend f) = f := by
  apply Subtype.ext
  ext z
  simp

/-- Restriction along an inclusion of open domains. -/
noncomputable def restrict (h : V ≤ U) : holomorphicFunctions U →ₐ[ℂ] holomorphicFunctions V :=
  ((ContinuousMap.compRightAlgHom ℂ ℂ
    ⟨Set.inclusion h, continuous_inclusion h⟩).comp (holomorphicFunctions U).val).codRestrict
      (holomorphicFunctions V) fun f =>
        ⟨extend f, (differentiableOn_extend f).mono h, fun z => extend_apply f (Set.inclusion h z)⟩

@[simp]
theorem restrict_apply (h : V ≤ U) (f : holomorphicFunctions U) (z : V) :
    (restrict h f).val z = f.val (Set.inclusion h z) := (rfl)

/-- Restriction agrees with restricting the same ambient representative. -/
@[simp]
theorem restrict_of (h : V ≤ U) (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g U) :
    restrict h (of U g hg) = of V g (hg.mono h) := by
  apply Subtype.ext
  ext z
  simp

@[simp]
theorem restrict_refl : restrict (le_refl U) = AlgHom.id ℂ (holomorphicFunctions U) := by
  ext f z
  simp

@[simp]
theorem restrict_comp (hVU : V ≤ U) (hWV : W ≤ V) :
    (restrict hWV).comp (restrict hVU) = restrict (hWV.trans hVU) := by
  ext f z
  simp

/-- Restriction is continuous for the compact-open topology. -/
theorem continuous_restrict (h : V ≤ U) : Continuous (restrict h) := by
  unfold restrict
  exact (ContinuousMap.compRightAlgHom_continuous ℂ ℂ
    ⟨Set.inclusion h, continuous_inclusion h⟩).comp continuous_subtype_val |>.subtype_mk _

/-- Convergence in the inherited topology is locally uniform convergence on the open domain. -/
theorem tendsto_iff_tendstoLocallyUniformlyOn {ι : Type*} {p : Filter ι}
    {F : ι → holomorphicFunctions U} {f : holomorphicFunctions U} :
    Tendsto F p (𝓝 f) ↔ TendstoLocallyUniformlyOn (fun i => extend (F i)) (extend f) p U := by
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  rw [tendsto_subtype_rng, ContinuousMap.tendsto_iff_tendstoLocallyUniformly,
    tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  simp only [Function.comp_def, extend_apply]
  rfl

/-- If a holomorphic function on `U` maps a subset `s ⊆ U` into an open set `V`, it maps a smaller
open neighbourhood `U' ≤ U` of `s` into `V`. -/
theorem exists_le_mapsTo_extend {s : Set ℂ} (hs : s ⊆ U) (f : holomorphicFunctions U)
    (hf : MapsTo (extend f) s V) :
    ∃ U' : Opens ℂ, s ⊆ U' ∧ U' ≤ U ∧ MapsTo (extend f) U' V := by
  refine ⟨⟨Subtype.val '' (f.val ⁻¹' (V : Set ℂ)),
    U.isOpen.isOpenMap_subtype_val _ (V.isOpen.preimage f.val.continuous)⟩,
    fun z hz => ⟨⟨z, hs hz⟩, ?_, rfl⟩, ?_, ?_⟩
  · rw [mem_preimage, ← extend_apply]
    exact hf hz
  · rintro _ ⟨z, -, rfl⟩
    exact z.property
  · rintro _ ⟨z, hz, rfl⟩
    rw [extend_apply]
    exact mem_preimage.mp hz

/-- Values of `f` on `U` lie in `V` when `extend f` maps `U` into `V`. -/
theorem apply_mem_of_mapsTo_extend (f : holomorphicFunctions U)
    (hf : MapsTo (extend f) U V) (z : U) : f.val z ∈ V := by
  rw [← extend_apply]
  exact hf z.property

/-- Postcomposition with holomorphic functions on `V` along a holomorphic map from `U` into `V`. -/
noncomputable def comp (f : holomorphicFunctions U) (hf : MapsTo (extend f) U V) :
    holomorphicFunctions V →ₐ[ℂ] holomorphicFunctions U :=
  ((ContinuousMap.compRightAlgHom ℂ ℂ
    (ContinuousMap.mk
      (fun z : U => (⟨f.val z, apply_mem_of_mapsTo_extend f hf z⟩ : V))
      (f.val.continuous.subtype_mk _))).comp (holomorphicFunctions V).val).codRestrict
      (holomorphicFunctions U) fun g =>
        ⟨extend g ∘ extend f, (differentiableOn_extend g).comp (differentiableOn_extend f) hf,
          fun z => by
            simp only [Function.comp_apply, AlgHom.comp_apply, Subalgebra.coe_val,
              ContinuousMap.compRightAlgHom_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
            rw [extend_apply f z, extend_apply g ⟨f.val z, apply_mem_of_mapsTo_extend f hf z⟩]⟩

@[simp]
theorem comp_apply (f : holomorphicFunctions U) (hf : MapsTo (extend f) U V)
    (g : holomorphicFunctions V) (z : U) :
    (comp f hf g).val z =
      g.val ⟨f.val z, apply_mem_of_mapsTo_extend f hf z⟩ := (rfl)

/-- On the domain `U`, the zero extension of `comp f hf g` is `extend g ∘ extend f`. -/
theorem extend_comp (f : holomorphicFunctions U) (hf : MapsTo (extend f) U V)
    (g : holomorphicFunctions V) {z : ℂ} (hz : z ∈ U) :
    extend (comp f hf g) z = extend g (extend f z) := by
  rw [extend_apply _ ⟨z, hz⟩, comp_apply, ← extend_apply g]
  congr 1
  exact (extend_apply f ⟨z, hz⟩).symm

/-- Composition with an ambient holomorphic representative agrees with function composition. -/
@[simp]
theorem comp_of (f : holomorphicFunctions U) (hf : MapsTo (extend f) U V)
    (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g V) :
    comp f hf (of V g hg) = of U (g ∘ extend f) (hg.comp (differentiableOn_extend f) hf) := by
  apply Subtype.ext
  ext z
  simp [Function.comp_apply]

/-- Composing the coordinate function on `V` with `f` recovers `f`. -/
theorem comp_id (f : holomorphicFunctions U) (hf : MapsTo (extend f) U V) :
    comp f hf (of V id differentiableOn_id) = f := by
  simp

/-- Restricting the domain commutes with postcomposition. -/
@[simp]
theorem restrict_comp_apply (hWU : W ≤ U) (f : holomorphicFunctions U)
    (hf : MapsTo (extend f) U V) (g : holomorphicFunctions V) :
    restrict hWU (comp f hf g) =
      comp (restrict hWU f)
        (fun z hz => by
          rw [extend_apply _ ⟨z, hz⟩, restrict_apply]
          exact extend_apply f ⟨z, hWU hz⟩ ▸ hf (hWU hz)) g := by
  apply Subtype.ext
  ext z
  simp only [restrict_apply, comp_apply]
  rfl

/-- Postcomposition along a holomorphic map is continuous for the compact-open topology. -/
@[continuity]
theorem continuous_comp (f : holomorphicFunctions U) (hf : MapsTo (extend f) U V) :
    Continuous (comp f hf) := by
  unfold comp
  exact (ContinuousMap.compRightAlgHom_continuous ℂ ℂ
    (ContinuousMap.mk
      (fun z : U => (⟨f.val z, apply_mem_of_mapsTo_extend f hf z⟩ : V))
      (f.val.continuous.subtype_mk _))).comp continuous_subtype_val |>.subtype_mk _

end HolomorphicFunctions

/-- The holomorphic functions form a closed subalgebra of the continuous functions. -/
theorem isClosed_holomorphicFunctions (U : Opens ℂ) :
    IsClosed (holomorphicFunctions U : Set C(U, ℂ)) := by
  refine isClosed_iff_forall_filter.mpr ?_
  intro f p hp hpSet hpnhds
  let : p.NeBot := hp
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let g : ℂ → ℂ := Function.extend Subtype.val f (fun _ => 0)
  apply mem_holomorphicFunctions_iff_extend.mpr
  have hconv : TendstoLocallyUniformly (fun k z => k z) f p :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hpnhds
  have hext : TendstoLocallyUniformlyOn
      (fun k : C(U, ℂ) => Function.extend Subtype.val k (fun _ => 0)) g p U := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    simp only [Function.comp_def, g, Subtype.val_injective.extend_apply]
    convert hconv using 1
  have hmem : ∀ᶠ k in p, k ∈ holomorphicFunctions U := le_principal_iff.mp hpSet
  exact hext.differentiableOn
    (hmem.mono fun k hk => mem_holomorphicFunctions_iff_extend.mp hk) U.isOpen

/-- Holomorphic functions are complete for compact convergence. -/
instance (U : Opens ℂ) : CompleteSpace (holomorphicFunctions U) := by
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  exact (isClosed_holomorphicFunctions U).completeSpace_coe

end TauCeti
