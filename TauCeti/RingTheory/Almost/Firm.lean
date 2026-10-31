/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.FiveLemma
public import Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Localization.HasLocalization
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import TauCeti.RingTheory.Almost.SerreClass

/-!
# Firm modules over a basic setup

Let `(V, m)` be a basic setup and `m~ = m ⊗[V] m`. Every `V`-module `M` carries the action map
`m~ ⊗[V] M → M`, `(x ⊗ y) ⊗ z ↦ (x * y) • z`, and `M` is *firm* if this map is bijective. Bhatt
uses firm modules as a model, with small Hom-types, of the category of almost `V`-modules
(Construction 4.1.5). This file carries out that construction: the functor `j^* : M ↦ m~ ⊗[V] M`
lands in firm modules, is right adjoint to the inclusion `j_!` of firm modules and left adjoint to
the fully faithful functor `j_* : N ↦ Hom_V(m~, N)`, and kills exactly the almost zero modules.
Firm modules are closed under kernels, cokernels and extensions, so they form an abelian category,
and `j^*` is an exact functor between abelian categories. Hence `j^*` is a localization functor for
the almost isomorphisms, which fixes the category of firm modules as the localized category of
`ModuleCat V` at `S.almostZero.isoModSerre`, with Hom-types in the universe of the `V`-modules.

The basic input is that `m~` is an idempotent `V`-module
(`TauCeti.Almost.BasicSetup.tildeTensorIdealEquiv`), so `m~` is itself firm. The flatness of `m~`
is used for the closure of firm modules under kernels and extensions, and to see that `m~ ⊗[V] −`
turns almost isomorphisms into isomorphisms.

## Main definitions

* `TauCeti.Almost.BasicSetup.tildeAct`: the action map `m~ ⊗[V] M → M`.
* `TauCeti.Almost.BasicSetup.IsFirm`: a module whose action map is bijective, and the
  corresponding object property `TauCeti.Almost.BasicSetup.isFirm` of `ModuleCat V`.
* `TauCeti.Almost.BasicSetup.Firm`: the full subcategory of firm `V`-modules.
* `TauCeti.Almost.BasicSetup.firm`: the functor `ModuleCat V ⥤ S.Firm`, `M ↦ m~ ⊗[V] M`.
* `TauCeti.Almost.BasicSetup.closure`: the functor `S.Firm ⥤ ModuleCat V`, `N ↦ Hom_V(m~, N)`.

## Main results

* `TauCeti.Almost.BasicSetup.isFirm_tilde` and `TauCeti.Almost.BasicSetup.isFirm_tilde_tensor`:
  `m~` and every module `m~ ⊗[V] M` are firm.
* `TauCeti.Almost.BasicSetup.isFirm_classical`, `TauCeti.Almost.BasicSetup.isFirm_zero_iff` and
  `TauCeti.Almost.BasicSetup.isFirm_self_iff`: every module is firm for the classical setup, only
  the zero module is firm for the zero setup, and `V` is firm only if `m = V`.
* `TauCeti.Almost.BasicSetup.IsFirm.subsingleton_of_isAlmostZero`: a firm almost zero module is
  zero.
* `TauCeti.Almost.BasicSetup.IsFirm.ker`, `TauCeti.Almost.BasicSetup.IsFirm.quotient_range` and
  `TauCeti.Almost.BasicSetup.IsFirm.of_exact`: firm modules are closed under kernels, cokernels
  and extensions.
* `TauCeti.Almost.BasicSetup.IsAlmostIso.bijective_of_isFirm`: an almost isomorphism between firm
  modules is bijective.
* `TauCeti.Almost.BasicSetup.firmInclusionAdj`: the inclusion of firm modules is left adjoint to
  `firm`.
* `TauCeti.Almost.BasicSetup.firmAdj`: `firm` is left adjoint to `closure`, and `closure` is fully
  faithful (`TauCeti.Almost.BasicSetup.fullyFaithfulClosure`).
* `TauCeti.Almost.BasicSetup.kernel_firm`: the modules sent to zero by `firm` are exactly the
  almost zero modules.
* `TauCeti.Almost.BasicSetup.isLocalization_firm` and `TauCeti.Almost.BasicSetup.hasLocalization`:
  `firm` is a localization functor for the almost isomorphisms, and the resulting choice of
  localized category, with Hom-types in the universe of the `V`-modules.

## References

* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, §4.1, Construction 4.1.5,
  Warning 4.1.6 and Proposition 4.1.7.
* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.2,
  Proposition 2.2.21.
-/
public section

open TensorProduct CategoryTheory

namespace TauCeti.Almost.BasicSetup

universe u

variable {V : Type u} [CommRing V] (S : BasicSetup V)

/-! ### The action map `m~ ⊗[V] M → M` -/

section tildeAct

variable (M : Type*) [AddCommGroup M] [Module V M] {N : Type*} [AddCommGroup N] [Module V N]

/-- The action map `m~ ⊗[V] M → M`, `(x ⊗ y) ⊗ z ↦ (x * y) • z`. -/
noncomputable def tildeAct : S.tilde ⊗[V] M →ₗ[V] M :=
  TensorProduct.lid V M ∘ₗ S.tildeMul.rTensor M

@[simp]
theorem tildeAct_tmul (t : S.tilde) (x : M) : S.tildeAct M (t ⊗ₜ x) = S.tildeMul t • x := by
  simp [tildeAct]

variable {M} in
/-- The action map is natural in the module. -/
theorem tildeAct_comp_lTensor (f : M →ₗ[V] N) :
    S.tildeAct N ∘ₗ f.lTensor S.tilde = f ∘ₗ S.tildeAct M :=
  TensorProduct.ext' fun t x ↦ by simp

/-- The image of the action map is `m • M`. -/
theorem range_tildeAct : LinearMap.range (S.tildeAct M) = S.ideal • ⊤ := by
  rw [tildeAct, LinearMap.range_comp, LinearMap.rTensor_range, range_tildeMul]
  exact Submodule.map_range_rTensor_subtype_lid

/-- Letting `m~` act on the first factor of `m~ ⊗[V] M` or through `M` gives the same map
`m~ ⊗[V] (m~ ⊗[V] M) → m~ ⊗[V] M`. -/
theorem lTensor_tildeAct :
    (S.tildeAct M).lTensor S.tilde = S.tildeAct (S.tilde ⊗[V] M) := by
  refine TensorProduct.ext' fun t u ↦ ?_
  induction u using TensorProduct.inductionOn with
  | add u u' hu hu' => rw [tmul_add, map_add, hu, hu', ← map_add, ← tmul_add]
  | tmul s x =>
    rw [LinearMap.lTensor_tmul, tildeAct_tmul, tildeAct_tmul, tmul_smul, smul_tmul',
      smul_tmul', tildeMul_smul_comm]

end tildeAct

/-! ### Firm modules -/

section IsFirm

variable (M : Type*) [AddCommGroup M] [Module V M] {N : Type*} [AddCommGroup N] [Module V N]

/-- A `V`-module `M` is *firm* for the basic setup `S` if the action map `m~ ⊗[V] M → M`,
`(x ⊗ y) ⊗ z ↦ (x * y) • z`, is bijective (Bhatt, Construction 4.1.5). -/
def IsFirm : Prop :=
  Function.Bijective (S.tildeAct M)

variable {S M} in
theorem isFirm_iff_bijective : S.IsFirm M ↔ Function.Bijective (S.tildeAct M) :=
  Iff.rfl

/-- Being firm is invariant under linear equivalence. -/
theorem _root_.LinearEquiv.isFirm_iff {M : Type*} [AddCommGroup M] [Module V M]
    (e : M ≃ₗ[V] N) : S.IsFirm M ↔ S.IsFirm N := by
  have h : S.tildeAct N =
      (e.toLinearMap ∘ₗ S.tildeAct M) ∘ₗ (e.lTensor S.tilde).symm.toLinearMap :=
    TensorProduct.ext' fun t y ↦ by simp
  rw [isFirm_iff_bijective, isFirm_iff_bijective, h, LinearMap.coe_comp, LinearMap.coe_comp,
    LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    Function.Bijective.of_comp_iff _ (LinearEquiv.bijective _),
    Function.Bijective.of_comp_iff' e.bijective]

/-- The module `m~` is firm: the action `m~ ⊗[V] m~ → m~` is bijective. -/
theorem isFirm_tilde : S.IsFirm S.tilde := by
  let e : S.tilde ⊗[V] S.tilde ≃ₗ[V] S.tilde :=
    (TensorProduct.assoc V S.tilde S.ideal S.ideal).symm ≪≫ₗ
      S.tildeTensorIdealEquiv.rTensor S.ideal ≪≫ₗ S.tildeTensorIdealEquiv
  have he : S.tildeAct S.tilde = e.toLinearMap := by
    refine TensorProduct.ext' fun t s ↦ ?_
    induction s using TensorProduct.inductionOn with
    | add s s' hs hs' => rw [tmul_add, map_add, map_add, hs, hs']
    | tmul c d =>
      rw [tildeAct_tmul, tildeMul_smul_comm]
      simp [e, smul_smul, mul_comm]
  rw [isFirm_iff_bijective, he]
  exact e.bijective

/-- For every module `M`, the module `m~ ⊗[V] M` is firm. -/
theorem isFirm_tilde_tensor : S.IsFirm (S.tilde ⊗[V] M) := by
  have h : S.tildeAct (S.tilde ⊗[V] M) =
      (S.tildeAct S.tilde).rTensor M ∘ₗ (TensorProduct.assoc V S.tilde S.tilde M).symm := by
    refine TensorProduct.ext' fun t u ↦ ?_
    induction u using TensorProduct.inductionOn with
    | add u u' hu hu' => rw [tmul_add, map_add, map_add, hu, hu']
    | tmul s x => simp [smul_tmul']
  rw [isFirm_iff_bijective, h, LinearMap.coe_comp, LinearEquiv.coe_coe]
  -- `LinearEquiv.ofBijective` and `LinearEquiv.rTensor` have the expected underlying maps.
  exact ((LinearEquiv.ofBijective _ S.isFirm_tilde).rTensor M).bijective.comp
    (LinearEquiv.bijective _)

variable {S M} in
/-- A firm module that is almost zero is zero: its action map is a surjection from
`m~ ⊗[V] M = 0`. -/
theorem IsFirm.subsingleton_of_isAlmostZero (hM : S.IsFirm M) (h : S.IsAlmostZero M) :
    Subsingleton M :=
  have := (S.isAlmostZero_iff_subsingleton_tilde_tensor M).mp h
  hM.surjective.subsingleton

/-- For the classical setup `(V, V)` every module is firm. -/
theorem isFirm_classical : (classical V).IsFirm M := by
  rw [isFirm_iff_bijective, tildeAct, LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact (TensorProduct.lid V M).bijective.comp
    ((LinearEquiv.ofBijective _ classical_tildeMul_bijective).rTensor M).bijective

/-- For the zero setup `(V, 0)` only the zero module is firm. -/
@[simp]
theorem isFirm_zero_iff : (zero V).IsFirm M ↔ Subsingleton M := by
  have : Subsingleton ((zero V).tilde ⊗[V] M) :=
    ((zero V).isAlmostZero_iff_subsingleton_tilde_tensor M).mp isAlmostZero_zero
  refine ⟨fun h ↦ h.surjective.subsingleton, fun _ ↦ ⟨fun _ _ _ ↦ Subsingleton.elim _ _,
    fun x ↦ ⟨0, Subsingleton.elim _ _⟩⟩⟩

/-- The ring `V` is firm only for the classical setup: the image of its action map is `m`. -/
theorem isFirm_self_iff : S.IsFirm V ↔ S.ideal = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := S.range_tildeAct V
    rwa [LinearMap.range_eq_top.mpr h.surjective, Ideal.smul_eq_mul, Ideal.mul_top,
      eq_comm] at this
  · obtain rfl : S = classical V := BasicSetup.ext (h.trans classical_ideal.symm)
    exact isFirm_classical V

end IsFirm

/-! ### Kernels, cokernels and extensions of firm modules -/

section Closure

variable {S} {M N P : Type*} [AddCommGroup M] [Module V M] [AddCommGroup N] [Module V N]
  [AddCommGroup P] [Module V P]

-- In the applications of the five lemma below, the tensor products are named explicitly: their
-- additive structure must be found as `AddCommGroup` instances, not unified from `→ₗ[V]`.

/-- The kernel of a linear map between firm modules is firm. This uses the flatness of `m~`. -/
theorem IsFirm.ker {f : M →ₗ[V] N} (hM : S.IsFirm M) (hN : S.IsFirm N) :
    S.IsFirm (LinearMap.ker f) :=
  isFirm_iff_bijective.mpr <| LinearMap.bijective_of_bijective_of_injective_of_left_exact
    (M₁ := S.tilde ⊗[V] LinearMap.ker f) (M₂ := S.tilde ⊗[V] M) (M₃ := S.tilde ⊗[V] N)
    ((LinearMap.ker f).subtype.lTensor S.tilde) (f.lTensor S.tilde) (LinearMap.ker f).subtype f
    (S.tildeAct _) (S.tildeAct M) (S.tildeAct N)
    (S.tildeAct_comp_lTensor _).symm (S.tildeAct_comp_lTensor _).symm
    (Module.Flat.lTensor_exact S.tilde (LinearMap.exact_subtype_ker_map f))
    (LinearMap.exact_subtype_ker_map f) (isFirm_iff_bijective.mp hM) hN.injective
    (Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _))
    (Submodule.injective_subtype _)

/-- The cokernel of a linear map between firm modules is firm. -/
theorem IsFirm.quotient_range {f : M →ₗ[V] N} (hM : S.IsFirm M) (hN : S.IsFirm N) :
    S.IsFirm (N ⧸ LinearMap.range f) :=
  isFirm_iff_bijective.mpr <| LinearMap.bijective_of_surjective_of_bijective_of_right_exact
    (M₁ := S.tilde ⊗[V] M) (M₂ := S.tilde ⊗[V] N) (M₃ := S.tilde ⊗[V] (N ⧸ LinearMap.range f))
    (f.lTensor S.tilde) ((LinearMap.range f).mkQ.lTensor S.tilde) f (LinearMap.range f).mkQ
    (S.tildeAct M) (S.tildeAct N) (S.tildeAct _)
    (S.tildeAct_comp_lTensor _).symm (S.tildeAct_comp_lTensor _).symm
    (lTensor_exact S.tilde f.exact_map_mkQ_range (Submodule.mkQ_surjective _))
    f.exact_map_mkQ_range hM.surjective (isFirm_iff_bijective.mp hN)
    (LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _)) (Submodule.mkQ_surjective _)

/-- Firm modules are closed under extensions: in a short exact sequence `0 → M → N → P → 0` with
`M` and `P` firm, `N` is firm. This uses the flatness of `m~`. -/
theorem IsFirm.of_exact {f : M →ₗ[V] N} {g : N →ₗ[V] P} (hfg : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hM : S.IsFirm M)
    (hP : S.IsFirm P) : S.IsFirm N :=
  isFirm_iff_bijective.mpr <|
    LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (M₂ := S.tilde ⊗[V] M) (M₃ := S.tilde ⊗[V] N) (M₄ := S.tilde ⊗[V] P)
    (0 : Unit →ₗ[V] S.tilde ⊗[V] M) (f.lTensor S.tilde) (g.lTensor S.tilde)
    (0 : S.tilde ⊗[V] P →ₗ[V] Unit) (0 : Unit →ₗ[V] M) f g (0 : P →ₗ[V] Unit)
    (0 : Unit →ₗ[V] Unit) (S.tildeAct M) (S.tildeAct N) (S.tildeAct P) (0 : Unit →ₗ[V] Unit)
    (by simp) (S.tildeAct_comp_lTensor _).symm (S.tildeAct_comp_lTensor _).symm (by simp)
    ((LinearMap.exact_zero_iff_injective (M := S.tilde ⊗[V] M) (N := S.tilde ⊗[V] N) _ _).mpr
      (Module.Flat.lTensor_preserves_injective_linearMap _ hf))
    (lTensor_exact S.tilde hfg hg)
    ((LinearMap.exact_zero_iff_surjective (M := S.tilde ⊗[V] N) (N := S.tilde ⊗[V] P) _ _).mpr
      (LinearMap.lTensor_surjective _ hg))
    ((LinearMap.exact_zero_iff_injective _ _).mpr hf) hfg
    ((LinearMap.exact_zero_iff_surjective _ _).mpr hg)
    (fun _ ↦ ⟨0, Subsingleton.elim _ _⟩) (isFirm_iff_bijective.mp hM)
    (isFirm_iff_bijective.mp hP) (fun _ _ _ ↦ Subsingleton.elim _ _)

end Closure

/-! ### Almost isomorphisms of firm modules -/

section IsAlmostIso

variable {S} {M N : Type*} [AddCommGroup M] [Module V M] [AddCommGroup N] [Module V N]

/-- Tensoring with `m~` turns an almost isomorphism into a bijection: `m~` is flat and
`m~ ⊗[V] −` kills almost zero modules. -/
theorem IsAlmostIso.lTensor_bijective {f : M →ₗ[V] N} (hf : S.IsAlmostIso f) :
    Function.Bijective (f.lTensor S.tilde) := by
  have h₁ := (S.isAlmostZero_iff_subsingleton_tilde_tensor _).mp (isAlmostIso_iff.mp hf).1
  have h₂ := (S.isAlmostZero_iff_subsingleton_tilde_tensor _).mp (isAlmostIso_iff.mp hf).2
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨z, rfl⟩ :=
      (Module.Flat.lTensor_exact S.tilde (LinearMap.exact_subtype_ker_map f) x).mp hx
    rw [Subsingleton.elim z 0, map_zero]
  · exact (lTensor_exact S.tilde f.exact_map_mkQ_range (Submodule.mkQ_surjective _) y).mp
      (Subsingleton.elim _ _)

/-- An almost isomorphism between firm modules is bijective. -/
theorem IsAlmostIso.bijective_of_isFirm {f : M →ₗ[V] N} (hf : S.IsAlmostIso f) (hM : S.IsFirm M)
    (hN : S.IsFirm N) : Function.Bijective f := by
  have h := congrArg DFunLike.coe (S.tildeAct_comp_lTensor f)
  rw [LinearMap.coe_comp, LinearMap.coe_comp] at h
  rw [← Function.Bijective.of_comp_iff f hM, ← h]
  exact hN.comp hf.lTensor_bijective

end IsAlmostIso

/-! ### The category of firm modules -/

section Category

/-- The firm `V`-modules, as an object property of `ModuleCat V`. -/
def isFirm : ObjectProperty (ModuleCat.{u} V) := fun M ↦ S.IsFirm M

@[simp]
theorem isFirm_iff (M : ModuleCat.{u} V) : S.isFirm M ↔ S.IsFirm M :=
  Iff.rfl

instance : S.isFirm.IsClosedUnderIsomorphisms :=
  ⟨fun e h ↦ (e.toLinearEquiv.isFirm_iff S).mp h⟩

/-- The category of firm `V`-modules, a full subcategory of `ModuleCat V`. Its inclusion
`S.isFirm.ι` is the functor `j_!` of Bhatt, Construction 4.1.5. -/
abbrev Firm : Type (u + 1) :=
  S.isFirm.FullSubcategory

/-- The functor `j^* : ModuleCat V ⥤ S.Firm`, `M ↦ m~ ⊗[V] M`, of Bhatt, Construction 4.1.5. -/
@[expose] noncomputable def firm : ModuleCat.{u} V ⥤ S.Firm :=
  S.isFirm.lift (MonoidalCategory.tensorLeft (ModuleCat.of V S.tilde)) fun M ↦
    (S.isFirm_iff _).mpr (S.isFirm_tilde_tensor M)

@[simp]
theorem firm_obj_obj (M : ModuleCat.{u} V) :
    (S.firm.obj M).obj = ModuleCat.of V (S.tilde ⊗[V] M) :=
  (rfl)

@[simp]
theorem firm_map_hom {M N : ModuleCat.{u} V} (f : M ⟶ N) :
    (S.firm.map f).hom = ModuleCat.ofHom (f.hom.lTensor S.tilde) :=
  (rfl)

/-- The inverse of the action map of a firm module. -/
private noncomputable def tildeActInv (N : S.Firm) : N.obj →ₗ[V] S.tilde ⊗[V] N.obj :=
  (LinearEquiv.ofBijective _ ((S.isFirm_iff _).mp N.property)).symm.toLinearMap

private theorem tildeAct_tildeActInv (N : S.Firm) (x : N.obj) :
    S.tildeAct N.obj (tildeActInv S N x) = x :=
  (LinearEquiv.ofBijective _ ((S.isFirm_iff _).mp N.property)).apply_symm_apply x

private theorem tildeActInv_naturality {N N' : S.Firm} (f : N ⟶ N') (x : N.obj) :
    tildeActInv S N' (f.hom.hom x) = f.hom.hom.lTensor S.tilde (tildeActInv S N x) := by
  apply ((S.isFirm_iff _).mp N'.property).injective
  rw [tildeAct_tildeActInv, ← LinearMap.comp_apply, S.tildeAct_comp_lTensor, LinearMap.comp_apply,
    tildeAct_tildeActInv]

/-- The inclusion of firm modules is left adjoint to `firm` (Bhatt, Construction 4.1.5). The
counit is the action map `m~ ⊗[V] M → M`, and the unit is the inverse of the action map of a firm
module. -/
noncomputable def firmInclusionAdj : S.isFirm.ι ⊣ S.firm where
  -- In the proofs below, `firm` acts on morphisms by `LinearMap.lTensor`, while `homMk` and
  -- `ModuleCat.ofHom` only wrap linear maps, so each component is the stated linear map.
  unit :=
    { app N := ObjectProperty.homMk (ModuleCat.ofHom (tildeActInv S N))
      naturality N N' f := by
        ext x
        exact tildeActInv_naturality S f x }
  counit :=
    { app M := ModuleCat.ofHom (S.tildeAct M)
      naturality M M' f := by
        ext t
        exact LinearMap.congr_fun (S.tildeAct_comp_lTensor f.hom) t }
  left_triangle_components N := by
    ext x
    exact tildeAct_tildeActInv S N x
  right_triangle_components M := by
    ext t
    have h : (S.tildeAct M).lTensor S.tilde (tildeActInv S (S.firm.obj M) t) = t := by
      rw [lTensor_tildeAct]
      exact tildeAct_tildeActInv S (S.firm.obj M) t
    exact h

/-- The counit of `firmInclusionAdj` is the action map `m~ ⊗[V] M → M`. -/
@[simp]
theorem firmInclusionAdj_counit_app_hom (M : ModuleCat.{u} V) :
    (S.firmInclusionAdj.counit.app M).hom = S.tildeAct M :=
  (rfl)

/-- The unit of `firmInclusionAdj` at a firm module `N` is the inverse of the action map of `N`. -/
theorem tildeAct_firmInclusionAdj_unit_app (N : S.Firm) (x : N.obj) :
    S.tildeAct N.obj ((S.firmInclusionAdj.unit.app N).hom.hom x) = x :=
  tildeAct_tildeActInv S N x

/-- The functor `firm` sends `M` to zero iff `M` is almost zero: `m~ ⊗[V] M = 0` iff `m • M = 0`.
-/
theorem isZero_firm_obj_iff (M : ModuleCat.{u} V) :
    Limits.IsZero (S.firm.obj M) ↔ S.IsAlmostZero M := by
  rw [isAlmostZero_iff_subsingleton_tilde_tensor, ← ModuleCat.isZero_of_iff_subsingleton (R := V)]
  -- `S.isFirm.ι.obj (S.firm.obj M)` is `ModuleCat.of V (S.tilde ⊗[V] M)` by `firm_obj_obj`.
  exact ⟨fun h ↦ S.isFirm.ι.map_isZero h,
    fun h ↦ Limits.IsZero.of_full_of_faithful_of_isZero S.isFirm.ι _ h⟩

/-- The modules sent to zero by `firm` are exactly the almost zero modules. -/
theorem kernel_firm : S.firm.kernel = S.almostZero := by
  ext M
  rw [Functor.kernel, ObjectProperty.prop_inverseImage_iff, almostZero_iff]
  exact S.isZero_firm_obj_iff M

/-- For every `V`-module `N`, the evaluation map `m~ ⊗[V] Hom_V(m~, N) → N`, `t ⊗ g ↦ g t`, the
counit of the tensor-hom adjunction for `m~`, is an almost isomorphism. -/
theorem isAlmostIso_ihom_ev_app (N : ModuleCat.{u} V) :
    S.IsAlmostIso ((ihom.ev (ModuleCat.of V S.tilde)).app N).hom := by
  -- We argue with any map `ev : m~ ⊗[V] Hom(m~, N) → N` sending `t ⊗ g` to `g t`; naming the
  -- source `m~ ⊗[V] Hom(m~, N)` lets us compute with pure tensors.
  suffices h : ∀ ev : ModuleCat.of V (S.tilde ⊗[V] (ModuleCat.of V S.tilde ⟶ N)) ⟶ N,
      (∀ t g, ev.hom (t ⊗ₜ g) = g.hom t) → S.IsAlmostIso ev.hom from
    h ((ihom.ev (ModuleCat.of V S.tilde)).app N) fun _ _ ↦ rfl
  intro ev hev
  -- `ψ n` is the map `t ↦ (x * y) • n` for `t = x ⊗ y`; the elements `ev (s ⊗ ψ n)` exhaust
  -- `m • N`.
  let ψ : N →ₗ[V] (ModuleCat.of V S.tilde ⟶ N) :=
    ModuleCat.homLinearEquiv.symm.toLinearMap ∘ₗ LinearMap.smulRightₗ S.tildeMul
  have hψ (n : N) (t : S.tilde) : (ψ n).hom t = S.tildeMul t • n := rfl
  have key (s : S.tilde) (x : S.tilde ⊗[V] (ModuleCat.of V S.tilde ⟶ N)) :
      S.tildeMul s • x = s ⊗ₜ ψ (ev.hom x) := by
    induction x using TensorProduct.inductionOn with
    | tmul t g =>
      rw [hev, smul_tmul', tildeMul_smul_comm, smul_tmul]
      congr 1
      refine ModuleCat.hom_ext (LinearMap.ext fun u ↦ ?_)
      rw [ModuleCat.hom_smul, LinearMap.smul_apply, hψ, ← map_smul, tildeMul_smul_comm, map_smul]
    | add x y hx hy => rw [smul_add, hx, hy, map_add, map_add, tmul_add]
  -- Every `ε ∈ m` kills the kernel and the cokernel of `ev`.
  refine isAlmostIso_iff.mpr ⟨isAlmostZero_iff.mpr fun ε hε x ↦ ?_,
    isAlmostZero_iff.mpr fun ε hε y ↦ ?_⟩
  all_goals
    rw [← range_tildeMul] at hε
    obtain ⟨s, rfl⟩ := hε
  · apply Subtype.ext
    -- The source of `ev` is `m~ ⊗[V] Hom(m~, N)` as a `ModuleCat`, so `key` applies up to defeq.
    refine (Submodule.coe_smul _ x).trans ((key s x).trans ?_)
    rw [LinearMap.mem_ker.mp x.2, map_zero, tmul_zero]
    rfl
  · induction y using Submodule.Quotient.induction_on with | _ n
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨s ⊗ₜ ψ n, (hev _ _).trans (hψ _ _)⟩

/-- The functor `j_* : S.Firm ⥤ ModuleCat V`, `N ↦ Hom_V(m~, N)`, of Bhatt, Construction 4.1.5. -/
@[expose] noncomputable def closure : S.Firm ⥤ ModuleCat.{u} V :=
  S.isFirm.ι ⋙ ihom (ModuleCat.of V S.tilde)

@[simp]
theorem closure_obj (N : S.Firm) :
    S.closure.obj N = (ihom (ModuleCat.of V S.tilde)).obj N.obj :=
  (rfl)

@[simp]
theorem closure_map {N N' : S.Firm} (f : N ⟶ N') :
    S.closure.map f = (ihom (ModuleCat.of V S.tilde)).map f.hom :=
  (rfl)

/-- The functor `firm` is left adjoint to `closure` (Bhatt, Construction 4.1.5): this is the
tensor-hom adjunction for `m~`, restricted to firm modules. -/
noncomputable def firmAdj : S.firm ⊣ S.closure :=
  (ihom.adjunction (ModuleCat.of V S.tilde)).restrictFullyFaithful (Functor.FullyFaithful.id _)
    S.isFirm.fullyFaithfulι (Iso.refl _) (Iso.refl _)

/-- The counit of `firmAdj` is the evaluation map `m~ ⊗[V] Hom_V(m~, N) → N`. -/
@[simp]
theorem firmAdj_counit_app_hom (N : S.Firm) :
    (S.firmAdj.counit.app N).hom = (ihom.ev (ModuleCat.of V S.tilde)).app N.obj := by
  have := (ihom.adjunction (ModuleCat.of V S.tilde)).map_restrictFullyFaithful_counit_app
    (L := S.firm) (R := S.closure)
    (Functor.FullyFaithful.id _) S.isFirm.fullyFaithfulι (Iso.refl _) (Iso.refl _) N
  simp only [closure, Functor.comp_obj, ObjectProperty.ι_obj, Functor.id_obj,
    ObjectProperty.ι_map, MonoidalCategory.curriedTensor_obj_obj, Iso.refl_inv, NatTrans.id_app,
    MonoidalCategory.curriedTensor_obj_map, MonoidalCategory.whiskerLeft_id,
    ihom.ihom_adjunction_counit, Category.id_comp] at this
  -- The remaining identity is `𝟙 (m~ ⊗ S.closure.obj N)`, written through `firm_obj_obj`.
  exact this.trans (Category.id_comp _)

/-- The unit of `firmAdj` is the coevaluation map `M → Hom_V(m~, m~ ⊗[V] M)`. -/
@[simp]
theorem firmAdj_unit_app (M : ModuleCat.{u} V) :
    S.firmAdj.unit.app M = (ihom.coev (ModuleCat.of V S.tilde)).app M := by
  have := (ihom.adjunction (ModuleCat.of V S.tilde)).map_restrictFullyFaithful_unit_app
    (L := S.firm) (R := S.closure)
    (Functor.FullyFaithful.id _) S.isFirm.fullyFaithfulι (Iso.refl _) (Iso.refl _) M
  simp only [Functor.id_obj, closure, Functor.comp_obj, ObjectProperty.ι_obj, Functor.id_map,
    MonoidalCategory.curriedTensor_obj_obj, ihom.ihom_adjunction_unit, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id] at this
  -- The remaining identity is `𝟙 (m~ ⊗ M)`, written through `firm_obj_obj`.
  exact this.trans ((congrArg _ ((ihom _).map_id _)).trans (Category.comp_id _))

/-- The counit `m~ ⊗[V] Hom_V(m~, N) → N` of `firmAdj` is an isomorphism for every firm module
`N`: it is an almost isomorphism between firm modules. -/
instance isIso_firmAdj_counit : IsIso S.firmAdj.counit := by
  have (N : S.Firm) : IsIso (S.firmAdj.counit.app N) := by
    have hbij : Function.Bijective (S.firmAdj.counit.app N).hom.hom := by
      rw [firmAdj_counit_app_hom]
      exact (S.isAlmostIso_ihom_ev_app N.obj).bijective_of_isFirm (S.isFirm_tilde_tensor _)
        ((S.isFirm_iff _).mp N.property)
    have : IsIso (S.isFirm.ι.map (S.firmAdj.counit.app N)) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr hbij
    exact isIso_of_fully_faithful S.isFirm.ι _
  exact NatIso.isIso_of_isIso_app _

/-- The functor `closure` is fully faithful (Bhatt, Construction 4.1.5). -/
noncomputable def fullyFaithfulClosure : S.closure.FullyFaithful :=
  S.firmAdj.fullyFaithfulROfIsIsoCounit

instance : S.closure.Full :=
  S.fullyFaithfulClosure.full

instance : S.closure.Faithful :=
  S.fullyFaithfulClosure.faithful

/-! ### The abelian category of firm modules -/

open Limits

instance : S.isFirm.ContainsZero where
  exists_zero := ⟨_, S.isFirm.ι.map_isZero ((S.isZero_firm_obj_iff (ModuleCat.of V PUnit)).mpr
    S.isAlmostZero_of_subsingleton), (S.firm.obj (ModuleCat.of V PUnit)).property⟩

instance : S.isFirm.IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    exact S.isFirm.prop_of_iso ((ModuleCat.kernelIsoKer f).symm ≪≫
      IsLimit.conePointUniqueUpToIso (limit.isLimit _) hk) (IsFirm.ker hX hY)

instance : S.isFirm.IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    exact S.isFirm.prop_of_iso ((ModuleCat.cokernelIsoRangeQuotient f).symm ≪≫
      IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hk) (IsFirm.quotient_range hX hY)

instance : S.isFirm.IsClosedUnderExtensions where
  prop_X₂_of_shortExact {T} hT h₁ h₃ :=
    IsFirm.of_exact ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp hT.exact)
      hT.moduleCat_injective_f hT.moduleCat_surjective_g h₁ h₃

instance : S.isFirm.IsClosedUnderBinaryProducts :=
  .mk' fun _ ⟨F, hF⟩ ↦ S.isFirm.prop_of_iso
    ((biprod.isoProd _ _).trans (HasLimit.isoOfNatIso (diagramIsoPair F)).symm)
    (S.isFirm.prop_biprod (hF _) (hF _))

/-- Firm modules are closed under finite products. With closure under kernels and cokernels, this
makes `S.Firm` an abelian category, with kernels and cokernels computed in `ModuleCat V`, by
Mathlib's instance for full subcategories. -/
instance : S.isFirm.IsClosedUnderFiniteProducts :=
  .mk'

/-- The functor `firm` is left exact, being right adjoint to the inclusion of firm modules. -/
instance : PreservesFiniteLimits S.firm :=
  have : PreservesLimitsOfSize.{0, 0} S.firm := S.firmInclusionAdj.rightAdjoint_preservesLimits
  inferInstance

/-- The functor `firm` is right exact, being left adjoint to `closure`. -/
instance : PreservesFiniteColimits S.firm :=
  have : PreservesColimitsOfSize.{0, 0} S.firm := S.firmAdj.leftAdjoint_preservesColimits
  inferInstance

/-- The functor `firm : ModuleCat V ⥤ S.Firm` is a localization functor for the almost
isomorphisms (Bhatt, Proposition 4.1.7(2); Gabber–Ramero, Proposition 2.2.21): it is exact with a
fully faithful right adjoint, and it kills exactly the almost zero modules. -/
instance isLocalization_firm : S.firm.IsLocalization S.almostZero.isoModSerre := by
  have := Abelian.isLocalization_isoModSerre_kernel_of_leftAdjoint S.firmAdj
  convert this using 2
  exact S.kernel_firm.symm

/-- The almost isomorphisms of `ModuleCat V` have a localization whose Hom-types live in the
universe of the `V`-modules: the category of firm modules, with `firm` as localization functor.
With this instance, the category of almost `V`-modules is the localized category
`S.almostZero.isoModSerre.Localization'`. -/
noncomputable instance hasLocalization :
    MorphismProperty.HasLocalization.{u}
      (S.almostZero : ObjectProperty (ModuleCat.{u} V)).isoModSerre where
  L := S.firm

end Category

end TauCeti.Almost.BasicSetup
