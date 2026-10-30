/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import TauCeti.RingTheory.Almost.BasicSetup

/-!
# Firm modules over a basic setup

Let `(V, m)` be a basic setup and `m~ = m ⊗[V] m`. Every `V`-module `M` carries the action map
`m~ ⊗[V] M → M`, `(x ⊗ y) ⊗ z ↦ (x * y) • z`, and `M` is *firm* if this map is bijective. Bhatt
uses firm modules as a model, with small Hom-types, of the category of almost `V`-modules
(Construction 4.1.5). This file proves the first steps of that construction: the functor
`M ↦ m~ ⊗[V] M` lands in firm modules, is right adjoint to the inclusion of firm modules, and kills
exactly the almost zero modules.

The basic input is that `m~` is an idempotent `V`-module: the map `m~ ⊗[V] m → m~`,
`t ⊗ z ↦ z • t`, is bijective, so `m~` is itself firm. This uses the flatness of `m~`; along the way
we see that `x ⊗ y = y ⊗ x` in `m~` (Gabber–Ramero, Claim 2.1.10).

## Main definitions

* `TauCeti.Almost.BasicSetup.tildeAct`: the action map `m~ ⊗[V] M → M`.
* `TauCeti.Almost.BasicSetup.tildeTensorIdealEquiv`: the linear equivalence `m~ ⊗[V] m ≃ m~`,
  `t ⊗ z ↦ z • t`.
* `TauCeti.Almost.BasicSetup.IsFirm`: a module whose action map is bijective, and the
  corresponding object property `TauCeti.Almost.BasicSetup.isFirm` of `ModuleCat V`.
* `TauCeti.Almost.BasicSetup.Firm`: the full subcategory of firm `V`-modules.
* `TauCeti.Almost.BasicSetup.firm`: the functor `ModuleCat V ⥤ S.Firm`, `M ↦ m~ ⊗[V] M`.

## Main results

* `TauCeti.Almost.BasicSetup.tmul_comm`: `x ⊗ y = y ⊗ x` in `m~`.
* `TauCeti.Almost.BasicSetup.isFirm_tilde` and `TauCeti.Almost.BasicSetup.isFirm_tilde_tensor`:
  `m~` and every module `m~ ⊗[V] M` are firm.
* `TauCeti.Almost.BasicSetup.isFirm_classical`, `TauCeti.Almost.BasicSetup.isFirm_zero_iff` and
  `TauCeti.Almost.BasicSetup.isFirm_self_iff`: every module is firm for the classical setup, only
  the zero module is firm for the zero setup, and `V` is firm only if `m = V`.
* `TauCeti.Almost.BasicSetup.IsFirm.subsingleton_of_isAlmostZero`: a firm almost zero module is
  zero.
* `TauCeti.Almost.BasicSetup.firmInclusionAdj`: the inclusion of firm modules is left adjoint to
  `firm`.
* `TauCeti.Almost.BasicSetup.kernel_firm`: the modules sent to zero by `firm` are exactly the
  almost zero modules.

## References

* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, §4.1, Construction 4.1.5 and
  Warning 4.1.6.
* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.1, Claim 2.1.10.
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
  refine le_antisymm ?_ (Submodule.smul_le.mpr fun r hr x _ ↦ ?_)
  · rw [LinearMap.range_le_iff_comap, eq_top_iff, ← TensorProduct.span_tmul_eq_top,
      Submodule.span_le]
    rintro _ ⟨t, x, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, tildeAct_tmul]
    refine Submodule.smul_mem_smul ?_ trivial
    rw [← coe_tildeToIdeal]
    exact (S.tildeToIdeal t).2
  · obtain ⟨t, ht⟩ := S.tildeToIdeal_surjective ⟨r, hr⟩
    refine ⟨t ⊗ₜ x, ?_⟩
    rw [tildeAct_tmul, ← coe_tildeToIdeal, ht]

/-- The two ways of letting `m~` act on itself agree: `(s₁ * s₂) • t = (t₁ * t₂) • s` for
`s = s₁ ⊗ s₂` and `t = t₁ ⊗ t₂` in `m~`. -/
theorem tildeMul_smul_comm (s t : S.tilde) : S.tildeMul s • t = S.tildeMul t • s := by
  induction s using TensorProduct.inductionOn with
  | add s s' hs hs' => rw [map_add, add_smul, hs, hs', smul_add]
  | tmul c d =>
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => rw [smul_add, ht, ht', map_add, add_smul]
    | tmul a b =>
      -- Both sides equal `c ⊗ (d * a * b)`.
      have h₁ : ((c : V) * d) • a = ((d : V) * a) • c :=
        Subtype.ext <| by simp only [Submodule.coe_smul, smul_eq_mul]; ring
      have h₂ : ((d : V) * a) • b = ((a : V) * b) • d :=
        Subtype.ext <| by simp only [Submodule.coe_smul, smul_eq_mul]; ring
      rw [tildeMul_tmul, tildeMul_tmul, smul_tmul', h₁, smul_tmul, h₂, tmul_smul]

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

/-! ### `m~` is an idempotent module -/

/-- The map `m~ ⊗[V] m → m~`, `t ⊗ z ↦ z • t`, is injective because `m~` is flat and surjective
because `m * m = m`. -/
private theorem bijective_rid_comp_lTensor_subtype :
    Function.Bijective
      ((TensorProduct.rid V S.tilde).toLinearMap ∘ₗ S.ideal.subtype.lTensor S.tilde) := by
  refine ⟨(TensorProduct.rid V S.tilde).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap _ S.ideal.injective_subtype), ?_⟩
  rw [← LinearMap.range_eq_top, eq_top_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
  rintro _ ⟨a, b, rfl⟩
  obtain ⟨u, rfl⟩ := S.tildeToIdeal_surjective a
  induction u using TensorProduct.inductionOn with
  | add u u' hu hu' => rw [map_add, add_tmul]; exact add_mem hu hu'
  | tmul x y =>
    refine ⟨(x ⊗ₜ b) ⊗ₜ y, ?_⟩
    have hxy : (y : V) • x = S.tildeToIdeal (x ⊗ₜ y) :=
      Subtype.ext (by simp [mul_comm])
    simp [smul_tmul', hxy]

/-- The linear equivalence `m~ ⊗[V] m ≃ m~`, `t ⊗ z ↦ z • t`: `m~` is an idempotent module. -/
noncomputable def tildeTensorIdealEquiv : S.tilde ⊗[V] S.ideal ≃ₗ[V] S.tilde :=
  LinearEquiv.ofBijective _ S.bijective_rid_comp_lTensor_subtype

@[simp]
theorem tildeTensorIdealEquiv_tmul (t : S.tilde) (z : S.ideal) :
    S.tildeTensorIdealEquiv (t ⊗ₜ z) = (z : V) • t := by
  rw [tildeTensorIdealEquiv, LinearEquiv.ofBijective_apply]
  simp

/-- The map `m ⊗[V] m~ → m~`, `z ⊗ t ↦ z • t`, is injective because `m~` is flat. -/
private theorem injective_lid_comp_rTensor_subtype :
    Function.Injective
      ((TensorProduct.lid V S.tilde).toLinearMap ∘ₗ S.ideal.subtype.rTensor S.tilde) :=
  (TensorProduct.lid V S.tilde).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap _ S.ideal.injective_subtype)

/-- The tensor factors of `m~ = m ⊗[V] m` commute: `x ⊗ y = y ⊗ x` (Gabber–Ramero, Claim 2.1.10).
-/
theorem tmul_comm (x y : S.ideal) : (x ⊗ₜ[V] y : S.tilde) = y ⊗ₜ x := by
  -- First, `x ⊗ (y ⊗ z) = y ⊗ (x ⊗ z)` in `m ⊗[V] m~`, as both have image `(x * y) ⊗ z` in `m~`.
  have h₁ (x y z : S.ideal) : x ⊗ₜ[V] (y ⊗ₜ[V] z) = y ⊗ₜ[V] (x ⊗ₜ[V] z) := by
    refine S.injective_lid_comp_rTensor_subtype ?_
    have hxy : (x : V) • y = (y : V) • x := Subtype.ext (by simp [mul_comm])
    simp [smul_tmul', hxy]
  -- Hence swapping the factors of `m~` is the identity on `m~ ⊗[V] m`, and so on `m~`, since
  -- `m~ ⊗[V] m → m~` is surjective.
  have h₂ : (TensorProduct.comm V S.ideal S.ideal).toLinearMap.rTensor S.ideal = LinearMap.id :=
    TensorProduct.ext_threefold fun x y z ↦
      (TensorProduct.assoc V S.ideal S.ideal S.ideal).injective (by simpa using h₁ y x z)
  have h₃ (w : S.tilde ⊗[V] S.ideal) :
      TensorProduct.comm V S.ideal S.ideal (S.tildeTensorIdealEquiv w) =
        S.tildeTensorIdealEquiv ((TensorProduct.comm V S.ideal S.ideal).toLinearMap.rTensor
          S.ideal w) := by
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp only [map_add, hw, hw']
    | tmul t z => simp
  obtain ⟨w, hw⟩ := S.tildeTensorIdealEquiv.surjective (x ⊗ₜ y)
  have h₄ := h₃ w
  rw [h₂, LinearMap.id_apply, hw, TensorProduct.comm_tmul] at h₄
  exact h₄.symm

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
  have h : Function.Bijective (classical V).tildeMul := by
    refine ⟨fun s t hst ↦ classical_tildeToIdeal_bijective.1 (Subtype.ext ?_), fun x ↦ ?_⟩
    · simpa only [coe_tildeToIdeal] using hst
    · obtain ⟨t, ht⟩ := classical_tildeToIdeal_bijective.2 ⟨x, by simp⟩
      exact ⟨t, by rw [← coe_tildeToIdeal, ht]⟩
  rw [isFirm_iff_bijective, tildeAct, LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact (TensorProduct.lid V M).bijective.comp
    ((LinearEquiv.ofBijective _ h).rTensor M).bijective

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

end Category

end TauCeti.Almost.BasicSetup
