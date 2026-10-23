/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.TensorProduct.Stalk.Basic

/-!
# Tensor products commute with stalks

For arbitrary presheaves of modules over a presheaf of commutative rings, the canonical tensor
stalk comparison is a linear equivalence. Its inverse tensors representatives on a common
neighborhood. Neither quasi-coherence nor finite presentation is needed. This is the local
algebra calculation used to compare tensor products after changing the base ring at a point.

The construction uses the germ universal property and the tensor universal property, following
the usual proof that tensor products commute with filtered colimits. Mathlib's
`TensorProduct.directLimitLeft` concerns a fixed scalar ring; here the scalar rings also vary.
The forward map is `PresheafOfModules.tensorStalkComparison`, and its germ equation determines
the equivalence. `TopCat.Presheaf.germ_eq` supplies independence of representatives.
-/

public section

open CategoryTheory Opposite TopologicalSpace TopCat.Presheaf
open scoped TensorProduct

universe u

namespace TauCeti

noncomputable section

open _root_.PresheafOfModules

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
  (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat.{u})) (x : X)

private abbrev T := PresheafOfModulesOfCommRing.Monoidal.tensorObj M N

private def pairSection (U : Opens X) (hxU : x ∈ U) (m : M.obj (op U))
    (V : Opens X) (hxV : x ∈ V) (n : N.obj (op V)) : ↑(TopCat.Presheaf.stalk (T M N).presheaf x) :=
  TopCat.Presheaf.germ (T M N).presheaf (U ⊓ V) x ⟨hxU, hxV⟩
    (M.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op m ⊗ₜ[R.obj (op (U ⊓ V))]
      N.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op n)

private theorem pairSection_eq (U : Opens X) (hxU : x ∈ U) (m : M.obj (op U))
    (V : Opens X) (hxV : x ∈ V) (n : N.obj (op V))
    (W : Opens X) (hxW : x ∈ W) (i : W ⟶ U) (j : W ⟶ V) :
    pairSection M N x U hxU m V hxV n =
      TopCat.Presheaf.germ (T M N).presheaf W x hxW
        (M.map i.op m ⊗ₜ[R.obj (op W)] N.map j.op n) := by
  let k : W ⟶ U ⊓ V := homOfLE (le_inf i.le j.le)
  erw [pairSection, ← TopCat.Presheaf.germ_res_apply (T M N).presheaf k x hxW]
  erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
  congr 1
  exact congrArg₂ (fun m n ↦ m ⊗ₜ[R.obj (op W)] n)
    (M.map_comp_apply (homOfLE inf_le_left : U ⊓ V ⟶ U).op k.op m).symm
    (N.map_comp_apply (homOfLE inf_le_right : U ⊓ V ⟶ V).op k.op n).symm

private theorem pairSection_congr
    {U U' V V' : Opens X} {hxU : x ∈ U} {hxU' : x ∈ U'}
    {hxV : x ∈ V} {hxV' : x ∈ V'}
    {m : M.obj (op U)} {m' : M.obj (op U')}
    {n : N.obj (op V)} {n' : N.obj (op V')}
    (hm : TopCat.Presheaf.germ M.presheaf U x hxU m =
      TopCat.Presheaf.germ M.presheaf U' x hxU' m')
    (hn : TopCat.Presheaf.germ N.presheaf V x hxV n =
      TopCat.Presheaf.germ N.presheaf V' x hxV' n') :
    pairSection M N x U hxU m V hxV n = pairSection M N x U' hxU' m' V' hxV' n' := by
  obtain ⟨A, hxA, i, i', hi⟩ := TopCat.Presheaf.germ_eq M.presheaf x hxU hxU' m m' hm
  obtain ⟨B, hxB, j, j', hj⟩ := TopCat.Presheaf.germ_eq N.presheaf x hxV hxV' n n' hn
  let a : A ⊓ B ⟶ A := homOfLE inf_le_left
  let b : A ⊓ B ⟶ B := homOfLE inf_le_right
  rw [pairSection_eq M N x U hxU m V hxV n (A ⊓ B) ⟨hxA, hxB⟩ (a ≫ i) (b ≫ j),
    pairSection_eq M N x U' hxU' m' V' hxV' n' (A ⊓ B) ⟨hxA, hxB⟩ (a ≫ i') (b ≫ j')]
  congr 1
  -- Germ equality is stated on the additive presheaf, whose section maps are the
  -- underlying semilinear restriction maps of the module presheaf.
  change M.map i.op m = M.map i'.op m' at hi
  change N.map j.op n = N.map j'.op n' at hj
  have hi := congrArg (M.map a.op) hi
  have hj := congrArg (N.map b.op) hj
  erw [M.map_comp_apply i.op a.op, M.map_comp_apply i'.op a.op,
    N.map_comp_apply j.op b.op, N.map_comp_apply j'.op b.op]
  exact congrArg₂ (fun m n ↦ m ⊗ₜ[R.obj (op (A ⊓ B))] n) hi hj

private def pair (m : ↑(TopCat.Presheaf.stalk M.presheaf x))
    (n : ↑(TopCat.Presheaf.stalk N.presheaf x)) :
    ↑(TopCat.Presheaf.stalk (T M N).presheaf x) :=
  let hm := TopCat.Presheaf.exists_germ_eq M.presheaf m
  let hn := TopCat.Presheaf.exists_germ_eq N.presheaf n
  pairSection M N x hm.choose hm.choose_spec.choose hm.choose_spec.choose_spec.choose
    hn.choose hn.choose_spec.choose hn.choose_spec.choose_spec.choose

private theorem pair_germ (U : Opens X) (hx : x ∈ U)
    (m : M.obj (op U)) (n : N.obj (op U)) :
    pair M N x (TopCat.Presheaf.germ M.presheaf U x hx m)
      (TopCat.Presheaf.germ N.presheaf U x hx n) =
      TopCat.Presheaf.germ (T M N).presheaf U x hx (m ⊗ₜ[R.obj (op U)] n) := by
  refine (pairSection_congr M N x
    (TopCat.Presheaf.exists_germ_eq M.presheaf _).choose_spec.choose_spec.choose_spec
    (TopCat.Presheaf.exists_germ_eq N.presheaf _).choose_spec.choose_spec.choose_spec).trans ?_
  simpa using pairSection_eq M N x U hx m U hx n U hx (𝟙 U) (𝟙 U)

private theorem pair_add_left (m m' : ↑(TopCat.Presheaf.stalk M.presheaf x))
    (n : ↑(TopCat.Presheaf.stalk N.presheaf x)) :
    pair M N x (m + m') n = pair M N x m n + pair M N x m' n := by
  obtain ⟨U, hxU, n, rfl⟩ := TopCat.Presheaf.exists_germ_eq N.presheaf n
  obtain ⟨V, hVU, hxV, m, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq M.presheaf m hxU
  obtain ⟨W, hWV, hxW, m', rfl⟩ := TopCat.Presheaf.exists_le_germ_eq M.presheaf m' hxV
  rw [← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE hWV) x hxW m,
    ← TopCat.Presheaf.germ_res_apply N.presheaf (homOfLE (hWV.trans hVU)) x hxW n]
  erw [← map_add, pair_germ, pair_germ, pair_germ, TensorProduct.add_tmul, map_add]

private theorem pair_add_right (m : ↑(TopCat.Presheaf.stalk M.presheaf x))
    (n n' : ↑(TopCat.Presheaf.stalk N.presheaf x)) :
    pair M N x m (n + n') = pair M N x m n + pair M N x m n' := by
  obtain ⟨U, hxU, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
  obtain ⟨V, hVU, hxV, n, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq N.presheaf n hxU
  obtain ⟨W, hWV, hxW, n', rfl⟩ := TopCat.Presheaf.exists_le_germ_eq N.presheaf n' hxV
  rw [← TopCat.Presheaf.germ_res_apply N.presheaf (homOfLE hWV) x hxW n,
    ← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE (hWV.trans hVU)) x hxW m]
  erw [← map_add, pair_germ, pair_germ, pair_germ, TensorProduct.tmul_add, map_add]

private theorem pair_smul_left (r : ↑(R.stalk x))
    (m : ↑(TopCat.Presheaf.stalk M.presheaf x)) (n : ↑(TopCat.Presheaf.stalk N.presheaf x)) :
    pair M N x (r • m) n = r • pair M N x m n := by
  obtain ⟨U, hxU, r, rfl⟩ := R.exists_germ_eq r
  obtain ⟨V, hVU, hxV, m, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq M.presheaf m hxU
  obtain ⟨W, hWV, hxW, n, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq N.presheaf n hxV
  rw [← R.germ_res_apply (homOfLE (hWV.trans hVU)) x hxW r,
    ← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE hWV) x hxW m]
  erw [← M.germ_smul (R := R) x W hxW, pair_germ, pair_germ,
    ← TensorProduct.smul_tmul', (T M N).germ_smul (R := R) x W hxW]

private theorem pair_smul_right (r : ↑(R.stalk x))
    (m : ↑(TopCat.Presheaf.stalk M.presheaf x)) (n : ↑(TopCat.Presheaf.stalk N.presheaf x)) :
    pair M N x m (r • n) = r • pair M N x m n := by
  obtain ⟨U, hxU, r, rfl⟩ := R.exists_germ_eq r
  obtain ⟨V, hVU, hxV, n, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq N.presheaf n hxU
  obtain ⟨W, hWV, hxW, m, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq M.presheaf m hxV
  rw [← R.germ_res_apply (homOfLE (hWV.trans hVU)) x hxW r,
    ← TopCat.Presheaf.germ_res_apply N.presheaf (homOfLE hWV) x hxW n]
  erw [← N.germ_smul (R := R) x W hxW, pair_germ, pair_germ,
    TensorProduct.tmul_smul, (T M N).germ_smul (R := R) x W hxW]

private def pairLinear : ↑(TopCat.Presheaf.stalk M.presheaf x) →ₗ[↑(R.stalk x)]
    ↑(TopCat.Presheaf.stalk N.presheaf x) →ₗ[↑(R.stalk x)]
      ↑(TopCat.Presheaf.stalk (T M N).presheaf x) where
  toFun m :=
    { toFun := pair M N x m
      map_add' := pair_add_right M N x m
      map_smul' := fun r n ↦ pair_smul_right M N x r m n }
  map_add' m m' := LinearMap.ext (pair_add_left M N x m m')
  map_smul' r m := LinearMap.ext (fun n ↦ pair_smul_left M N x r m n)

private def inverse :
    ↑(TopCat.Presheaf.stalk M.presheaf x) ⊗[↑(R.stalk x)]
      ↑(TopCat.Presheaf.stalk N.presheaf x) →ₗ[
    ↑(R.stalk x)] ↑(TopCat.Presheaf.stalk (T M N).presheaf x) :=
  TensorProduct.lift (pairLinear M N x)

private theorem inverse_tmul_germ (U : Opens X) (hx : x ∈ U)
    (m : M.obj (op U)) (n : N.obj (op U)) :
    inverse M N x (TopCat.Presheaf.germ M.presheaf U x hx m ⊗ₜ[↑(R.stalk x)]
      TopCat.Presheaf.germ N.presheaf U x hx n) =
      TopCat.Presheaf.germ (T M N).presheaf U x hx (m ⊗ₜ[R.obj (op U)] n) :=
  pair_germ M N x U hx m n

/-- Tensoring sections and then passing to germs agrees with tensoring their germs, as a linear
equivalence over the ring stalk. No finiteness or sheaf condition is needed. -/
def _root_.PresheafOfModules.tensorStalkEquiv :
    ↑(TopCat.Presheaf.stalk
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj M N).presheaf x) ≃ₗ[↑(R.stalk x)]
      ↑(TopCat.Presheaf.stalk M.presheaf x) ⊗[↑(R.stalk x)] ↑(TopCat.Presheaf.stalk N.presheaf x) :=
  LinearEquiv.ofLinearMap (tensorStalkComparison M N x) (inverse M N x)
    (by
      apply TensorProduct.ext'
      intro m n
      obtain ⟨U, hxU, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
      obtain ⟨V, hVU, hxV, n, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq N.presheaf n hxU
      rw [← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE hVU) x hxV m]
      -- The additive-presheaf carrier is the underlying module carrier.
      erw [LinearMap.comp_apply, inverse_tmul_germ, tensorStalkComparison_germ_tmul]
      rfl)
    (by
      apply LinearMap.ext
      intro t
      obtain ⟨U, hx, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq (T M N).presheaf t
      induction t using TensorProduct.inductionOn with
      | tmul m n =>
          erw [LinearMap.comp_apply, tensorStalkComparison_germ_tmul, inverse_tmul_germ]
          rfl
      | add a b ha hb =>
          -- The additive germ map is seen through the concrete-category wrapper.
          erw [map_add, map_add]
          exact congrArg₂ (· + ·) ha hb)

/-- The tensor stalk equivalence is the canonical comparison. -/
@[simp]
theorem _root_.PresheafOfModules.tensorStalkEquiv_apply
    (t : ↑(TopCat.Presheaf.stalk (PresheafOfModulesOfCommRing.Monoidal.tensorObj M N).presheaf x)) :
    tensorStalkEquiv M N x t = tensorStalkComparison M N x t := (rfl)

/-- The canonical tensor stalk comparison is bijective for arbitrary presheaves of modules. -/
theorem _root_.PresheafOfModules.tensorStalkComparison_bijective :
    Function.Bijective (tensorStalkComparison M N x) :=
  (tensorStalkEquiv M N x).bijective

/-- The inverse tensor stalk equivalence sends a tensor of germs from a common neighborhood
to the germ of the tensor of their representatives. -/
@[simp]
theorem _root_.PresheafOfModules.tensorStalkEquiv_symm_tmul_germ
    (U : Opens X) (hx : x ∈ U) (m : M.obj (op U)) (n : N.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe, CategoryTheory.Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj]
    ((tensorStalkEquiv M N x).symm (TopCat.Presheaf.germ M.presheaf U x hx m ⊗ₜ[↑(R.stalk x)]
      TopCat.Presheaf.germ N.presheaf U x hx n) =
      TopCat.Presheaf.germ
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj M N).presheaf U x hx
        (m ⊗ₜ[R.obj (op U)] n)) :=
  inverse_tmul_germ M N x U hx m n

/-- The tensor stalk equivalence commutes with morphisms in both factors. -/
theorem _root_.PresheafOfModules.tensorStalkEquiv_naturality
    {M' N' : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat.{u})}
    (f : M ⟶ M') (g : N ⟶ N') :
    (tensorStalkEquiv M' N' x).toLinearMap.comp
        (stalkMapCommRing x (PresheafOfModulesOfCommRing.Monoidal.tensorHom f g)) =
      (TensorProduct.map (stalkMapCommRing x f) (stalkMapCommRing x g)).comp
        (tensorStalkEquiv M N x).toLinearMap := by
  apply LinearMap.ext
  intro t
  obtain ⟨U, hx, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq (T M N).presheaf t
  induction t using TensorProduct.inductionOn with
  | tmul m n =>
      -- Tensor sections and their additive-presheaf carriers coincide; the germ
      -- computation lemmas retain the explicit module carriers.
      erw [LinearMap.comp_apply, LinearEquiv.coe_coe, stalkMapCommRing_germ,
        PresheafOfModulesOfCommRing.Monoidal.tensorHom_app,
        ModuleCat.MonoidalCategory.tensorHom_tmul, tensorStalkEquiv_apply,
        tensorStalkComparison_germ_tmul, LinearMap.comp_apply, LinearEquiv.coe_coe,
        tensorStalkEquiv_apply, tensorStalkComparison_germ_tmul, TensorProduct.map_tmul,
        stalkMapCommRing_germ, stalkMapCommRing_germ]
  | add a b ha hb =>
      erw [map_add, map_add, map_add]
      exact congrArg₂ (· + ·) ha hb

end

end TauCeti
