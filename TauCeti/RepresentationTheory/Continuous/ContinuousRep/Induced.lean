/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Hom
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Continuous induction from an open subgroup

Let `H` be an open subgroup of a topological group `Γ` and `σ` a jointly continuous
representation of `H` on an `A`-module `U`. The *induced module* `indV H σ` consists of the
continuous functions `f : Γ → U` with `f (h * x) = σ h (f x)`; it is Mathlib's
`ContRepresentation.coindV` along the inclusion `H → Γ`, with the compact-open topology. The
*induced representation* `ind H σ` lets `g` act by `(g • f) x = f (x * g)`; its operators are
those of Mathlib's `ContRepresentation.coind`.

Because `H` is open, every function `f : Γ → U` with `f (h * x) = σ h (f x)` is continuous: near
a point `x` it is `y ↦ σ (y * x⁻¹) (f x)` on the open coset `H * x`. A version with parameters
shows that, for a right transversal `S` of `H` (Mathlib's `Subgroup.IsComplement`), evaluation on
`S` is an `A`-linear homeomorphism from `indV H σ` onto `S → U`, with inverse
`u ↦ (h * s ↦ σ h (u s))`. So for `H` of finite index the topology on `indV H σ` is the module
topology when the one on `U` is. For `Γ` locally compact the action of `Γ` on `indV H σ` is
jointly continuous, so `ind H σ` is a `TauCeti.ContinuousRep`, functorial in `σ`. Its invariants
are the constant functions with value in `U^H`, so evaluation at `1` identifies them with the
invariants of `σ`. The element `e_u` supported on `H`, with `e_u h = σ h u`, generates the induced
module: for `H` of finite index every element is a sum of translates of such elements, one for each
coset of `H`.

## Main definitions

* `TauCeti.ContinuousRep.indV`: the induced module.
* `TauCeti.ContinuousRep.transversalExtend`: the equivariant extension `h * s ↦ σ h (u s)` of
  values on a right transversal.
* `TauCeti.ContinuousRep.indVMk`: the element of the induced module given by an equivariant
  function, which is automatically continuous.
* `TauCeti.ContinuousRep.ind`: the induced continuous representation.
* `TauCeti.ContinuousRep.Hom.ind`, `TauCeti.ContinuousRep.Iso.ind`: functoriality of induction.
* `TauCeti.ContinuousRep.indSingle`: the element `e_u` of the induced module supported on `H`.
* `TauCeti.ContinuousRep.indVEquivPi`: evaluation on a right transversal, as a linear
  homeomorphism `indV H σ ≃L[A] (S → U)`.
* `TauCeti.ContinuousRep.indInvariantsEquiv`: Shapiro's lemma on invariants,
  `(ind H σ)^Γ ≃ U^H` by evaluation at `1`.

## Main results

* `TauCeti.ContinuousRep.continuous_of_apply_mul`: an `H`-equivariant function out of `Γ` is
  continuous; `TauCeti.ContinuousRep.continuous_uncurry_of_apply_mul` is the version jointly in a
  parameter on which it depends continuously.
* `TauCeti.ContinuousRep.toContRepresentation_ind`: the operators of `ind H σ` are those of
  Mathlib's `ContRepresentation.coind`.
* `TauCeti.ContinuousRep.isModuleTopology_indV`: for a finite right transversal, the topology of
  the induced module is the module topology.
* `TauCeti.ContinuousRep.finrank_indV`: the induced module has rank `[Γ : H] · rank U`.
* `TauCeti.ContinuousRep.ind_apply_indSingle`: `h • e_u = e_{σ h u}` for `h ∈ H`.
* `TauCeti.ContinuousRep.Hom.ind_indSingle`: naturality of `e_u`, `f.ind e_u = e_{f u}`.
* `TauCeti.ContinuousRep.finsum_ind_indSingle`: every element of the induced module is the sum of
  its pieces on the cosets of `H`.
-/

public section

open Topology

namespace TauCeti

namespace ContinuousRep

section Continuity

variable {Γ A U : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Semiring A]
  [AddCommMonoid U] [Module A U] [TopologicalSpace U] {H : Subgroup Γ}

/-- **Equivariant functions are continuous.** Let `H` be an open subgroup of `Γ` and `σ` a jointly
continuous representation of `H`. A family `F p : Γ → U` with `F p (h * x) = σ h (F p x)`,
continuous in `p` at each point of `Γ`, is jointly continuous: near `(p₀, x)` it is
`(p, y) ↦ σ (y * x⁻¹) (F p x)`. -/
theorem continuous_uncurry_of_apply_mul {P : Type*} [TopologicalSpace P]
    (σ : ContinuousRep H A U) (hH : IsOpen (H : Set Γ)) {F : P → Γ → U}
    (hF : ∀ p (h : H) x, F p (h * x) = σ h (F p x))
    (hc : ∀ x, Continuous fun p => F p x) : Continuous fun q : P × Γ => F q.1 q.2 := by
  refine continuous_iff_continuousAt.2 fun ⟨p₀, x⟩ => ?_
  -- on `P × H`, the translate `(p, y) ↦ F p (y * x)` is `σ y (F p x)`
  have hk : ContinuousOn (fun q : P × Γ => F q.1 (q.2 * x)) (Set.univ ×ˢ (H : Set Γ)) := by
    have e : (Set.univ ×ˢ (H : Set Γ)).domRestrict (fun q : P × Γ => F q.1 (q.2 * x)) =
        fun q => σ ⟨q.val.2, q.property.2⟩ (F q.val.1 x) :=
      funext fun q => hF q.val.1 ⟨q.val.2, q.property.2⟩ x
    rw [continuousOn_iff_continuous_domRestrict, e]
    exact Continuous.continuousRep_apply σ
      ((continuous_snd.comp continuous_subtypeVal).subtype_mk _)
      ((hc x).comp (continuous_fst.comp continuous_subtypeVal))
  have h1 : ContinuousAt (fun q : P × Γ => F q.1 (q.2 * x)) (p₀, 1) :=
    hk.continuousAt (prod_mem_nhds Filter.univ_mem (hH.mem_nhds H.one_mem))
  have h2 : ContinuousAt (fun q : P × Γ => (q.1, q.2 * x⁻¹)) (p₀, x) := by fun_prop
  have := ContinuousAt.comp_of_eq h1 h2 (by simp)
  simpa [Function.comp_def] using this

/-- **Equivariant functions are continuous.** For an open subgroup `H` of `Γ`, every function
`f : Γ → U` with `f (h * x) = σ h (f x)` is continuous. -/
theorem continuous_of_apply_mul (σ : ContinuousRep H A U) (hH : IsOpen (H : Set Γ))
    {f : Γ → U} (hf : ∀ (h : H) x, f (h * x) = σ h (f x)) : Continuous f :=
  (continuous_uncurry_of_apply_mul (P := Unit) σ hH (F := fun _ => f) (fun _ => hf)
    fun _ => continuous_const).comp
    (continuous_const.prodMk continuous_id : Continuous fun x : Γ => ((), x))

section Transversal

variable {S : Set Γ} (σ : ContinuousRep H A U) (hS : Subgroup.IsComplement (H : Set Γ) S)

/-- The equivariant function `h * s ↦ σ h (u s)` attached to values `u : S → U` on a right
transversal `S`. -/
noncomputable def transversalExtend (u : S → U) (x : Γ) : U :=
  σ (hS.equiv x).1 (u (hS.equiv x).2)

omit [IsTopologicalGroup Γ] in
/-- The extension from a right transversal at `x` is `σ h (u s)`, where `x = h * s` is the
decomposition of `x` along `H` and the transversal. -/
theorem transversalExtend_apply (u : S → U) (x : Γ) :
    transversalExtend σ hS u x = σ (hS.equiv x).1 (u (hS.equiv x).2) := (rfl)

omit [IsTopologicalGroup Γ] in
/-- The extension from a right transversal is `H`-equivariant. -/
theorem transversalExtend_mul (u : S → U) (h : H) (x : Γ) :
    transversalExtend σ hS u (h * x) = σ h (transversalExtend σ hS u x) := by
  rw [transversalExtend_apply, transversalExtend_apply, hS.equiv_mul_left h x, map_mul,
    mul_apply_eq_comp]

omit [IsTopologicalGroup Γ] in
/-- The extension from a right transversal takes the prescribed values on the transversal. -/
theorem transversalExtend_apply_of_mem (u : S → U) {s : Γ} (hs : s ∈ S) :
    transversalExtend σ hS u s = u ⟨s, hs⟩ := by
  have h1 := Subgroup.IsComplement.equiv_fst_eq_one_of_mem_of_one_mem hS H.one_mem hs
  have h2 := Subgroup.IsComplement.equiv_snd_eq_self_of_mem_of_one_mem hS H.one_mem hs
  rw [transversalExtend_apply, h1, h2]
  exact congr($(map_one σ) (u ⟨s, hs⟩))

omit [IsTopologicalGroup Γ] in
/-- The extension from a right transversal at a point `s : S` is `u s`. -/
@[simp]
theorem transversalExtend_apply_coe (u : S → U) (s : S) :
    transversalExtend σ hS u s = u s :=
  transversalExtend_apply_of_mem σ hS u s.property

/-- For an open subgroup, the extension from a right transversal is jointly continuous in the
values and the point. -/
theorem continuous_transversalExtend (hH : IsOpen (H : Set Γ)) :
    Continuous fun q : (S → U) × Γ => transversalExtend σ hS q.1 q.2 :=
  continuous_uncurry_of_apply_mul σ hH (fun u h x => transversalExtend_mul σ hS u h x)
    fun _ => (σ.continuous_apply _).comp (_root_.continuous_apply _)

end Transversal

end Continuity

section Ring

variable {Γ A U : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [Ring A] [TopologicalSpace A] [AddCommGroup U] [Module A U] [TopologicalSpace U]
  [IsTopologicalAddGroup U] [ContinuousSMul A U] {H : Subgroup Γ}


section Induced

variable (H) in
/-- **The induced module.** The continuous functions `f : Γ → U` with `f (h * x) = σ h (f x)`,
with the compact-open topology: Mathlib's `ContRepresentation.coindV` along the inclusion of
`H`. -/
abbrev indV (σ : ContinuousRep H A U) : Submodule A C(Γ, U) :=
  σ.toContRepresentation.coindV (ContinuousMonoidHom.subgroupSubtype H)

omit [IsTopologicalGroup Γ] in
theorem mem_indV {σ : ContinuousRep H A U} (f : C(Γ, U)) :
    f ∈ indV H σ ↔ ∀ (h : H) x, f (h * x) = σ h (f x) := by
  simp

/-- The element of the induced module given by an equivariant function, which is continuous
because `H` is open. -/
def indVMk (σ : ContinuousRep H A U) (hH : IsOpen (H : Set Γ)) (f : Γ → U)
    (hf : ∀ (h : H) x, f (h * x) = σ h (f x)) : indV H σ :=
  ⟨⟨f, continuous_of_apply_mul σ hH hf⟩, (mem_indV _).2 hf⟩

@[simp]
theorem indVMk_apply (σ : ContinuousRep H A U) (hH : IsOpen (H : Set Γ)) (f : Γ → U)
    (hf : ∀ (h : H) x, f (h * x) = σ h (f x)) (x : Γ) :
    (indVMk σ hH f hf : C(Γ, U)) x = f x :=
  (rfl)

variable [LocallyCompactSpace Γ]

variable (H) in
/-- **The induced continuous representation.** `Γ` acts on the induced module by
`(g • f) x = f (x * g)`. For `Γ` locally compact the action is jointly continuous, since
composition of continuous maps is. -/
noncomputable def ind (σ : ContinuousRep H A U) : ContinuousRep Γ A (indV H σ) where
  toRepresentation :=
    (σ.toContRepresentation.coind (ContinuousMonoidHom.subgroupSubtype H)).toRepresentation
  continuous_action := by
    have hr : Continuous fun g : Γ => ContinuousMap.mulRight g :=
      (ContinuousMap.mk (fun q : Γ × Γ => q.2 * q.1) (by fun_prop)).curry.continuous
    refine continuous_induced_rng.2 <| (ContinuousMap.continuous_comp'.comp
      (hr.fst'.prodMk (continuous_subtypeVal.comp continuous_snd))).congr fun p => ?_
    exact (ContRepresentation.coind_apply_coe _ _ p.1 p.2).symm

@[simp]
theorem ind_apply_apply (σ : ContinuousRep H A U) (g : Γ) (f : indV H σ) (x : Γ) :
    (ind H σ g f : C(Γ, U)) x = (f : C(Γ, U)) (x * g) :=
  (rfl)

/-- **Agreement with Mathlib's coinduction.** The operators of the induced continuous
representation are those of Mathlib's `ContRepresentation.coind`. -/
theorem toContRepresentation_ind (σ : ContinuousRep H A U) :
    (ind H σ).toContRepresentation =
      σ.toContRepresentation.coind (ContinuousMonoidHom.subgroupSubtype H) :=
  DFunLike.ext _ _ fun _ => ContinuousLinearMap.ext fun _ => by
    rw [toContRepresentation_apply]
    rfl

end Induced

section Functoriality

variable [LocallyCompactSpace Γ]

variable {V W : Type*} [AddCommGroup V] [Module A V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul A V] [AddCommGroup W] [Module A W]
  [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul A W]
  {σ : ContinuousRep H A U} {τ : ContinuousRep H A V} {υ : ContinuousRep H A W}

/-- **Functoriality of induction.** A morphism `f : σ ⟶ τ` of continuous representations of `H`
induces the morphism `φ ↦ f ∘ φ` of induced representations. -/
noncomputable def Hom.ind (f : Hom σ τ) :
    Hom (ContinuousRep.ind H σ) (ContinuousRep.ind H τ) where
  toFun φ := ⟨(⟨f, f.cont⟩ : C(U, V)).comp φ, (mem_indV _).2 fun h x => by
    simp [(mem_indV _).1 φ.property h x, f.isIntertwining]⟩
  map_add' _ _ := Subtype.ext (ContinuousMap.ext fun _ => map_add f _ _)
  map_smul' _ _ := Subtype.ext (ContinuousMap.ext fun _ => map_smul f _ _)
  isIntertwining' g := LinearMap.ext fun φ => Subtype.ext (ContinuousMap.ext fun x => by simp)
  cont := ((ContinuousMap.continuous_postcomp _).comp continuous_subtypeVal).subtype_mk _

@[simp]
theorem Hom.ind_apply_apply (f : Hom σ τ) (φ : indV H σ) (x : Γ) :
    (f.ind φ : C(Γ, V)) x = f ((φ : C(Γ, U)) x) := by
  rw [← Hom.coe_toIntertwiningMap]
  rfl

@[simp]
theorem Hom.ind_id : (Hom.id σ).ind = Hom.id (ContinuousRep.ind H σ) :=
  Hom.ext fun _ => Subtype.ext (ContinuousMap.ext fun _ => by simp)

@[simp]
theorem Hom.ind_comp (f : Hom τ υ) (f' : Hom σ τ) : (f.comp f').ind = f.ind.comp f'.ind :=
  Hom.ext fun _ => Subtype.ext (ContinuousMap.ext fun _ => by simp)

/-- **Functoriality of induction** for isomorphisms: an isomorphism `σ ≅ τ` induces an
isomorphism of induced representations. -/
noncomputable def Iso.ind (e : Iso σ τ) :
    Iso (ContinuousRep.ind H σ) (ContinuousRep.ind H τ) where
  toRepresentationEquiv :=
    { e.toHom.ind.toIntertwiningMap with
      invFun := e.symm.toHom.ind
      left_inv φ := Subtype.ext (ContinuousMap.ext fun x => by simp)
      right_inv φ := Subtype.ext (ContinuousMap.ext fun x => by simp) }
  continuous_toFun := e.toHom.ind.cont
  continuous_invFun := e.symm.toHom.ind.cont

@[simp]
theorem Iso.ind_apply_apply (e : Iso σ τ) (φ : indV H σ) (x : Γ) :
    (e.ind φ : C(Γ, V)) x = e ((φ : C(Γ, U)) x) := by
  rw [← Iso.coe_toRepresentationEquiv, ← e.coe_toHom]
  rfl

@[simp]
theorem Iso.ind_toHom (e : Iso σ τ) : e.ind.toHom = e.toHom.ind :=
  Hom.ext fun _ => Subtype.ext (ContinuousMap.ext fun _ => by simp)

@[simp]
theorem Iso.symm_ind (e : Iso σ τ) : e.ind.symm = e.symm.ind :=
  Iso.ext fun φ => e.ind.injective (Subtype.ext (ContinuousMap.ext fun _ => by simp))

end Functoriality

section Single

variable (σ : ContinuousRep H A U) (hH : IsOpen (H : Set Γ))

/-- The equivariant function supported on `H` with value `σ h u` at `h ∈ H`. -/
private noncomputable def indSingleFun (u : U) (x : Γ) : U :=
  open Classical in if hx : x ∈ H then σ ⟨x, hx⟩ u else 0

omit [IsTopologicalGroup Γ] [TopologicalSpace A]
  [IsTopologicalAddGroup U] [ContinuousSMul A U] in
private theorem indSingleFun_of_mem (u : U) {x : Γ} (hx : x ∈ H) :
    indSingleFun σ u x = σ ⟨x, hx⟩ u := by
  simp [indSingleFun, hx]

omit [IsTopologicalGroup Γ] [TopologicalSpace A]
  [IsTopologicalAddGroup U] [ContinuousSMul A U] in
private theorem indSingleFun_of_notMem (u : U) {x : Γ} (hx : x ∉ H) : indSingleFun σ u x = 0 := by
  simp [indSingleFun, hx]

omit [IsTopologicalGroup Γ] [TopologicalSpace A]
  [IsTopologicalAddGroup U] [ContinuousSMul A U] in
private theorem indSingleFun_mul (u : U) (h : H) (x : Γ) :
    indSingleFun σ u (h * x) = σ h (indSingleFun σ u x) := by
  by_cases hx : x ∈ H
  · rw [indSingleFun_of_mem σ u (H.mul_mem h.property hx), indSingleFun_of_mem σ u hx,
      ← mul_apply_eq_comp, ← map_mul, show (⟨h * x, _⟩ : H) = h * ⟨x, hx⟩ from Subtype.ext rfl]
  · rw [indSingleFun_of_notMem σ u hx, map_zero,
      indSingleFun_of_notMem σ u fun hm => hx ((H.mul_mem_cancel_left h.property).1 hm)]

/-- The element `e_u` of the induced module supported on the open subgroup `H`, with value `σ h u`
at `h ∈ H`. -/
noncomputable def indSingle : U →L[A] indV H σ where
  toFun u := indVMk σ hH (indSingleFun σ u) (indSingleFun_mul σ u)
  map_add' u v := Subtype.ext (ContinuousMap.ext fun x => by
    by_cases hx : x ∈ H <;> simp [indSingleFun, hx])
  map_smul' a u := Subtype.ext (ContinuousMap.ext fun x => by
    by_cases hx : x ∈ H <;> simp [indSingleFun, hx])
  cont := by
    refine Continuous.subtype_mk ?_ _
    refine ((ContinuousMap.mk _ (continuous_uncurry_of_apply_mul σ hH
      (F := fun u => indSingleFun σ u) (fun u => indSingleFun_mul σ u) fun x => ?_)).curry
      |>.continuous).congr fun u => ContinuousMap.ext fun x =>
      (indVMk_apply σ hH _ (indSingleFun_mul σ u) x).symm
    by_cases hx : x ∈ H
    · simpa [indSingleFun, hx] using σ.continuous_apply ⟨x, hx⟩
    · simpa [indSingleFun, hx] using continuous_const

private theorem indSingle_apply (u : U) (x : Γ) :
    (indSingle σ hH u : C(Γ, U)) x = indSingleFun σ u x :=
  indVMk_apply σ hH _ (indSingleFun_mul σ u) x

@[simp]
theorem indSingle_apply_of_mem (u : U) {x : Γ} (hx : x ∈ H) :
    (indSingle σ hH u : C(Γ, U)) x = σ ⟨x, hx⟩ u := by
  rw [indSingle_apply, indSingleFun_of_mem]

@[simp]
theorem indSingle_apply_of_notMem (u : U) {x : Γ} (hx : x ∉ H) :
    (indSingle σ hH u : C(Γ, U)) x = 0 := by
  rw [indSingle_apply, indSingleFun_of_notMem σ u hx]

variable [LocallyCompactSpace Γ]

/-- An element `h ∈ H` acts on `e_u` by acting on `u`: `h • e_u = e_{σ h u}`. -/
@[simp]
theorem ind_apply_indSingle (h : H) (u : U) :
    ind H σ h (indSingle σ hH u) = indSingle σ hH (σ h u) := by
  refine Subtype.ext (ContinuousMap.ext fun x => ?_)
  rw [ind_apply_apply]
  by_cases hx : x ∈ H
  · rw [indSingle_apply_of_mem σ hH u (H.mul_mem hx h.property), indSingle_apply_of_mem σ hH _ hx,
      ← mul_apply_eq_comp, ← map_mul, show (⟨x * h, _⟩ : H) = ⟨x, hx⟩ * h from Subtype.ext rfl]
  · rw [indSingle_apply_of_notMem σ hH _ hx, indSingle_apply_of_notMem σ hH u fun hm =>
      hx ((H.mul_mem_cancel_right h.property).1 hm)]

variable {σ} in
/-- **Naturality of `e_u`.** The morphism induced by `f : σ ⟶ τ` sends `e_u` to `e_{f u}`. -/
@[simp]
theorem Hom.ind_indSingle {V : Type*} [AddCommGroup V] [Module A V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul A V] {τ : ContinuousRep H A V} (f : Hom σ τ)
    (u : U) :
    f.ind (indSingle σ hH u) = indSingle τ hH (f u) := by
  refine Subtype.ext (ContinuousMap.ext fun x => ?_)
  rw [Hom.ind_apply_apply]
  by_cases hx : x ∈ H
  · rw [indSingle_apply_of_mem σ hH u hx, indSingle_apply_of_mem τ hH _ hx, f.isIntertwining]
  · rw [indSingle_apply_of_notMem σ hH u hx, indSingle_apply_of_notMem τ hH _ hx, map_zero]

/-- **Decomposition along the cosets.** For `H` open of finite index, every element `φ` of the
induced module is the sum over `x H ∈ Γ / H` of the translates `x • e_{φ x⁻¹}`, the piece of `φ`
supported on the coset `H x⁻¹`. -/
theorem finsum_ind_indSingle [H.FiniteIndex] (φ : indV H σ) :
    ∑ᶠ q : Γ ⧸ H, ind H σ q.out (indSingle σ hH ((φ : C(Γ, U)) q.out⁻¹)) = φ := by
  have := Fintype.ofFinite (Γ ⧸ H)
  rw [finsum_eq_sum_of_fintype]
  refine Subtype.ext (ContinuousMap.ext fun x => ?_)
  rw [Submodule.coe_sum, ContinuousMap.sum_apply,
    Finset.sum_eq_single_of_mem ((x⁻¹ : Γ) : Γ ⧸ H) (Finset.mem_univ _)]
  · have hmem : x * Quotient.out ((x⁻¹ : Γ) : Γ ⧸ H) ∈ H := by
      simpa using QuotientGroup.eq.1 (QuotientGroup.out_eq' ((x⁻¹ : Γ) : Γ ⧸ H)).symm
    rw [ind_apply_apply, indSingle_apply_of_mem σ hH _ hmem, ← (mem_indV _).1 φ.property]
    simp
  · intro q _ hq
    rw [ind_apply_apply, indSingle_apply_of_notMem σ hH]
    -- `x * q.out ∈ H` would put `q.out` in the coset `x⁻¹ H`
    intro hm
    exact hq ((QuotientGroup.out_eq' q).symm.trans
      (QuotientGroup.eq.2 (by simpa using H.inv_mem hm)))

end Single

section Transversal

variable {S : Set Γ} (σ : ContinuousRep H A U) (hH : IsOpen (H : Set Γ))
  (hS : Subgroup.IsComplement (H : Set Γ) S)

/-- **The transversal isomorphism.** For a right transversal `S` of the open subgroup `H`,
evaluation on `S` is an `A`-linear homeomorphism from the induced module onto `S → U`, with
inverse `u ↦ (h * s ↦ σ h (u s))`. -/
noncomputable def indVEquivPi : indV H σ ≃L[A] (S → U) where
  toFun f s := (f : C(Γ, U)) s
  invFun u := ⟨⟨transversalExtend σ hS u,
      (continuous_transversalExtend σ hS hH).comp (continuous_const.prodMk continuous_id)⟩,
    (mem_indV _).2 (transversalExtend_mul σ hS u)⟩
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)
  left_inv f := by
    refine Subtype.ext (ContinuousMap.ext fun x => ?_)
    have := (mem_indV _).1 f.property (hS.equiv x).1 (hS.equiv x).2
    rw [Subgroup.IsComplement.equiv_fst_mul_equiv_snd] at this
    exact this.symm
  right_inv u := funext fun s => transversalExtend_apply_coe σ hS u s
  continuous_toFun := continuous_pi fun s =>
    (continuous_eval_const (s : Γ)).comp continuous_subtypeVal
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (ContinuousMap.mk _ (continuous_transversalExtend σ hS hH)).curry.continuous

@[simp]
theorem indVEquivPi_apply (f : indV H σ) (s : S) :
    indVEquivPi σ hH hS f s = (f : C(Γ, U)) s :=
  (rfl)

@[simp]
theorem indVEquivPi_symm_apply (u : S → U) (x : Γ) :
    ((indVEquivPi σ hH hS).symm u : C(Γ, U)) x = transversalExtend σ hS u x :=
  (rfl)

include hH hS in
/-- **The topology of the induced module is the module topology.** For an open subgroup with a
finite right transversal, if `U` carries the module topology then so does the induced module. -/
theorem isModuleTopology_indV [Finite S] [IsModuleTopology A U] :
    IsModuleTopology A (indV H σ) :=
  IsModuleTopology.iso (indVEquivPi σ hH hS).symm

include hH hS in
/-- **The rank of the induced module.** For a finite right transversal `S` and `U` free of
finite rank, the induced module has rank `#S · rank U`. -/
theorem finrank_indV [StrongRankCondition A] [Module.Free A U] [Module.Finite A U] [Finite S] :
    Module.finrank A (indV H σ) = Nat.card S * Module.finrank A U := by
  have := Fintype.ofFinite S
  rw [(indVEquivPi σ hH hS).toLinearEquiv.finrank_eq]
  simp [Module.finrank_pi_fintype, Nat.card_eq_fintype_card]

end Transversal

end Ring

section Invariants

variable {Γ A U : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [LocallyCompactSpace Γ] [CommRing A] [TopologicalSpace A] [AddCommGroup U] [Module A U]
  [TopologicalSpace U] [IsTopologicalAddGroup U] [ContinuousSMul A U] {H : Subgroup Γ}

/-- A `Γ`-invariant element of the induced module is a constant function: `f x = f 1`. -/
theorem ind_apply_eq_apply_one_of_mem_invariants {σ : ContinuousRep H A U}
    (f : (ind H σ).toRepresentation.invariants) (x : Γ) :
    (f.val : C(Γ, U)) x = (f.val : C(Γ, U)) 1 := by
  have hc := congr_arg (fun F : indV H σ => (F : C(Γ, U)) 1) (f.property x)
  simp only [coe_toRepresentation, ind_apply_apply, one_mul] at hc
  exact hc

/-- **Shapiro's lemma on invariants.** Evaluation at `1` identifies the invariants of the induced
representation with the invariants of `σ`. A `Γ`-invariant `f` is constant, `f x = f 1`, and
`f 1 = f h = σ h (f 1)`; conversely each `H`-invariant vector gives a constant function. -/
noncomputable def indInvariantsEquiv (σ : ContinuousRep H A U) :
    (ind H σ).toRepresentation.invariants ≃ₗ[A] σ.toRepresentation.invariants where
  toFun f := ⟨(f.val : C(Γ, U)) 1, fun h => by
    have h1 := (mem_indV _).1 f.val.property h 1
    rw [mul_one] at h1
    exact h1.symm.trans (ind_apply_eq_apply_one_of_mem_invariants f h)⟩
  invFun u := ⟨⟨ContinuousMap.const Γ u.val,
      (mem_indV _).2 fun h x => by simpa using (u.property h).symm⟩,
    fun _ => Subtype.ext (ContinuousMap.ext fun _ => (rfl))⟩
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)
  left_inv f := Subtype.ext (Subtype.ext (ContinuousMap.ext fun x =>
    (ind_apply_eq_apply_one_of_mem_invariants f x).symm))
  right_inv _ := (rfl)

@[simp]
theorem indInvariantsEquiv_apply (σ : ContinuousRep H A U)
    (f : (ind H σ).toRepresentation.invariants) :
    (indInvariantsEquiv σ f : U) = (f.val : C(Γ, U)) 1 :=
  (rfl)

@[simp]
theorem indInvariantsEquiv_symm_apply (σ : ContinuousRep H A U)
    (u : σ.toRepresentation.invariants) (x : Γ) :
    (((indInvariantsEquiv σ).symm u).val : C(Γ, U)) x = u :=
  (rfl)

end Invariants

end ContinuousRep

end TauCeti
