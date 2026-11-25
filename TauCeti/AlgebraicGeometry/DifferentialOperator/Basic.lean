/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import TauCeti.AlgebraicGeometry.Modules.Sections
public import TauCeti.RingTheory.Derivation.DifferentialOperator.Basic

/-!
# The sheaf of differential operators on a scheme

Let `k` be a commutative ring and `X` a scheme over `Spec k`. The sections of `O_X` over each
open `U` form a `k`-algebra (`Scheme.algebraOfOver`, through
`Scheme.baseRingToStructurePresheaf`), compatibly with restriction, so `O_X` is a
sheaf of `k`-modules: the presheaf of `k`-modules of sections
`(Scheme.Modules.sectionsBasePresheafFunctor k).obj (SheafOfModules.unit X.ringCatSheaf)` of the
unit sheaf of modules. A section of the sheaf of `k`-linear
endomorphisms of `O_X` over `U` is an element `D` of the ring `X.StructureEnd k U`: a family of
`k`-linear maps `Γ(X, V) → Γ(X, V)` for the opens `V ⊆ U`, compatible with restriction, and
multiplied by composition. Its component on `V` is `Scheme.endApp D V`.

Following Grothendieck (EGA IV₄, §16.8), `D` has order at most `m` when every component
`Scheme.endApp D V` lies in `TauCeti.differentialOperators k Γ(X, V) Γ(X, V) Γ(X, V) m`, that
is, when its iterated commutators with `m + 1` sections of `O_X` over `V` vanish. These form
the subsheaf `F_m D_X = X.differentialOperators k m` of the sheaf of endomorphisms
(`Scheme.isSheaf_differentialOperators`). The sheaf of differential operators `D_X` consists of
the endomorphisms that are locally of order at most some `m`; it is a sheaf of rings
`X.sheafOfDifferentialOperators k` under composition, with the ring map
`X.toPresheafOfDifferentialOperators k` from `O_X` sending a section to multiplication by it.

## Main results

* `Scheme.differentialOperators_mono`, `Scheme.mul_mem_differentialOperators`: the filtration
  `F_m D_X` is increasing and `F_p D_X ⬝ F_q D_X ⊆ F_(p+q) D_X`; restriction to smaller opens
  preserves the order (`Scheme.restrictEnd_mem_differentialOperators`).
* `Scheme.mem_differentialOperators_zero_iff`, `Scheme.toStructureEnd_injective` and
  `Scheme.differentialOperatorsZeroIso`: the operators of order zero are exactly the
  multiplications by sections of `O_X`, so `F_0 D_X = O_X`.
* `Scheme.isSheaf_differentialOperators`: the order of an operator is local on `X`.
* `Scheme.sheafOfDifferentialOperators`: the sheaf of rings `D_X`, with the ring map
  `Scheme.toPresheafOfDifferentialOperators` from `O_X`.

The `k`-algebra structure on sections is a definition rather than a global instance (see
`TauCeti.AlgebraicGeometry.Modules.GlobalSections`), activated locally in this file.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
-/

public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (k : Type u) [CommRing k] [X.Over (Spec (.of k))]

attribute [local instance] algebraOfOver

/-- The ring of `k`-linear endomorphisms of the structure sheaf restricted to an open `U`: a
family of `k`-linear maps `Γ(X, V) → Γ(X, V)` for the opens `V ⊆ U`, compatible with restriction.
Multiplication is composition. -/
abbrev StructureEnd (U : X.Opens) : Type u :=
  End ((Over.forget U).op ⋙
    (Modules.sectionsBasePresheafFunctor k).obj (SheafOfModules.unit X.ringCatSheaf))

variable {X k}

/-- The component on the sections over `V` of an endomorphism `D` of the structure sheaf
restricted to `U`, for `V` an open subset of `U`. -/
noncomputable def endApp {U : X.Opens} (D : X.StructureEnd k U) (V : Over U) :
    Γ(X, V.left) →ₗ[k] Γ(X, V.left) :=
  (D.asHom.app (op V)).hom

section endApp

variable {U : X.Opens}

@[simp]
theorem endApp_mul (D E : X.StructureEnd k U) (V : Over U) :
    endApp (D * E) V = endApp D V ∘ₗ endApp E V :=
  (rfl)

@[simp]
theorem endApp_one (V : Over U) : endApp (1 : X.StructureEnd k U) V = LinearMap.id :=
  (rfl)

@[simp]
theorem endApp_add (D E : X.StructureEnd k U) (V : Over U) :
    endApp (D + E) V = endApp D V + endApp E V :=
  (rfl)

@[simp]
theorem endApp_neg (D : X.StructureEnd k U) (V : Over U) : endApp (-D) V = -endApp D V :=
  (rfl)

@[simp]
theorem endApp_zero (V : Over U) : endApp (0 : X.StructureEnd k U) V = 0 :=
  (rfl)

/-- The components of an endomorphism commute with restriction. -/
theorem endApp_naturality (D : X.StructureEnd k U) {V W : Over U} (j : W ⟶ V)
    (f : Γ(X, V.left)) :
    X.presheaf.map j.left.op (endApp D V f) = endApp D W (X.presheaf.map j.left.op f) :=
  (congr($(D.asHom.naturality j.op) f)).symm

@[ext]
theorem StructureEnd.ext {D E : X.StructureEnd k U} (h : ∀ V, endApp D V = endApp E V) :
    D = E :=
  End.ext (NatTrans.ext (funext fun V ↦ ModuleCat.hom_ext (h V.unop)))

/-- An endomorphism of the structure sheaf restricted to `U`, from its components on the opens
`V ⊆ U`, given compatibility with restriction. -/
noncomputable def StructureEnd.ofApp (app : ∀ V : Over U, Γ(X, V.left) →ₗ[k] Γ(X, V.left))
    (naturality : ∀ {V W : Over U} (j : W ⟶ V) (f : Γ(X, V.left)),
      X.presheaf.map j.left.op (app V f) = app W (X.presheaf.map j.left.op f)) :
    X.StructureEnd k U :=
  End.of
    { app V := ModuleCat.ofHom (X := Γ(X, V.unop.left)) (Y := Γ(X, V.unop.left)) (app V.unop)
      naturality V W j := by
        ext f
        exact (naturality j.unop f).symm }

@[simp]
theorem endApp_ofApp (app : ∀ V : Over U, Γ(X, V.left) →ₗ[k] Γ(X, V.left))
    (naturality : ∀ {V W : Over U} (j : W ⟶ V) (f : Γ(X, V.left)),
      X.presheaf.map j.left.op (app V f) = app W (X.presheaf.map j.left.op f)) (V : Over U) :
    endApp (StructureEnd.ofApp app naturality) V = app V :=
  (rfl)

end endApp

variable (X k) in
/-- The presheaf of `k`-linear endomorphisms of the structure sheaf: its sections over `U` are
the endomorphisms of `O_X` restricted to `U`, and restriction restricts the family of components.
It is the internal hom `presheafHom` of the structure sheaf as a presheaf of `k`-modules
(`Scheme.Modules.sectionsBasePresheafFunctor` applied to the unit sheaf of modules) with itself,
with sections viewed as elements of the ring `X.StructureEnd k U`. -/
noncomputable abbrev endPresheaf : X.Opensᵒᵖ ⥤ Type u :=
  (presheafHom ((Modules.sectionsBasePresheafFunctor k).obj (SheafOfModules.unit X.ringCatSheaf))
    ((Modules.sectionsBasePresheafFunctor k).obj (SheafOfModules.unit X.ringCatSheaf))).copyObj
    (fun U ↦ X.StructureEnd k U.unop) fun _ ↦ Equiv.toIso End.homEquiv.symm

variable (X k) in
/-- The endomorphisms of the structure sheaf form a sheaf: they glue, since `O_X` does. -/
theorem isSheaf_endPresheaf :
    Presieve.IsSheaf (Opens.grothendieckTopology X) (X.endPresheaf k) :=
  Presieve.isSheaf_iso _ (Functor.isoCopyObj _ _ _) ((isSheaf_iff_isSheaf_of_type _ _).1
    (Presheaf.IsSheaf.hom _ _ (Modules.isSheaf_sectionsBasePresheafFunctor_obj k _)))

variable (k) in
/-- Restriction of endomorphisms of the structure sheaf from `U` to an open subset `U'`. -/
noncomputable def restrictEnd {U U' : X.Opens} (i : U' ⟶ U) :
    X.StructureEnd k U →+* X.StructureEnd k U' where
  toFun D := (X.endPresheaf k).map i.op D
  map_one' := (rfl)
  map_mul' _ _ := (rfl)
  map_zero' := (rfl)
  map_add' _ _ := (rfl)

@[simp]
theorem endApp_restrictEnd {U U' : X.Opens} (i : U' ⟶ U) (D : X.StructureEnd k U)
    (V : Over U') : endApp (X.restrictEnd k i D) V = endApp D ((Over.map i).obj V) :=
  (rfl)

@[simp]
theorem restrictEnd_id {U : X.Opens} (D : X.StructureEnd k U) :
    X.restrictEnd k (𝟙 U) D = D :=
  congr($((X.endPresheaf k).map_id (op U)) D)

@[simp]
theorem restrictEnd_restrictEnd {U U' U'' : X.Opens} (i : U' ⟶ U) (j : U'' ⟶ U')
    (D : X.StructureEnd k U) :
    X.restrictEnd k j (X.restrictEnd k i D) = X.restrictEnd k (j ≫ i) D :=
  congr($((X.endPresheaf k).map_comp i.op j.op) D).symm

/-! ### The order filtration -/

variable (X k) in
/-- The subsheaf `F_m D_X` of differential operators of order at most `m`: an endomorphism of
the structure sheaf restricted to `U` has order at most `m` when its component on every open
`V ⊆ U` has order at most `m` over `Γ(X, V)`, that is, when its iterated commutators with
`m + 1` sections of `O_X` over `V` vanish. -/
noncomputable def differentialOperators (m : ℕ) : Subfunctor (X.endPresheaf k) where
  obj U := {D : X.StructureEnd k U.unop | ∀ V : Over U.unop,
    endApp D V ∈ TauCeti.differentialOperators k Γ(X, V.left) Γ(X, V.left) Γ(X, V.left) m}
  map i _ hD V := hD ((Over.map i.unop).obj V)

theorem mem_differentialOperators_iff {m : ℕ} {U : X.Opens} {D : X.StructureEnd k U} :
    D ∈ (X.differentialOperators k m).obj (op U) ↔ ∀ V : Over U,
      endApp D V ∈ TauCeti.differentialOperators k Γ(X, V.left) Γ(X, V.left) Γ(X, V.left) m :=
  Iff.rfl

theorem differentialOperators_mono : Monotone (X.differentialOperators k) :=
  fun _ _ h _ _ hD V ↦ TauCeti.differentialOperators_mono h (hD V)

theorem zero_mem_differentialOperators (m : ℕ) (U : X.Opens) :
    (0 : X.StructureEnd k U) ∈ (X.differentialOperators k m).obj (op U) :=
  fun _ ↦ zero_mem _

theorem one_mem_differentialOperators (m : ℕ) (U : X.Opens) :
    (1 : X.StructureEnd k U) ∈ (X.differentialOperators k m).obj (op U) :=
  fun _ ↦ TauCeti.differentialOperators_mono (Nat.zero_le m)
    (TauCeti.mem_differentialOperators_zero_iff.2 fun _ _ ↦ rfl)

/-- Sums of operators of order at most `m` have order at most `m`. -/
theorem add_mem_differentialOperators {m : ℕ} {U : X.Opens} {D E : X.StructureEnd k U}
    (hD : D ∈ (X.differentialOperators k m).obj (op U))
    (hE : E ∈ (X.differentialOperators k m).obj (op U)) :
    D + E ∈ (X.differentialOperators k m).obj (op U) :=
  fun V ↦ add_mem (hD V) (hE V)

theorem neg_mem_differentialOperators {m : ℕ} {U : X.Opens} {D : X.StructureEnd k U}
    (hD : D ∈ (X.differentialOperators k m).obj (op U)) :
    -D ∈ (X.differentialOperators k m).obj (op U) :=
  fun V ↦ neg_mem (hD V)

/-- The composite of an operator of order at most `p` with one of order at most `q` has order
at most `p + q`. -/
theorem mul_mem_differentialOperators {p q : ℕ} {U : X.Opens} {D E : X.StructureEnd k U}
    (hD : D ∈ (X.differentialOperators k p).obj (op U))
    (hE : E ∈ (X.differentialOperators k q).obj (op U)) :
    D * E ∈ (X.differentialOperators k (p + q)).obj (op U) :=
  fun V ↦ by
    rw [endApp_mul]
    exact TauCeti.comp_mem_differentialOperators (hD V) (hE V)

/-- Restriction to an open subset preserves the order. -/
theorem restrictEnd_mem_differentialOperators {m : ℕ} {U U' : X.Opens} (i : U' ⟶ U)
    {D : X.StructureEnd k U} (hD : D ∈ (X.differentialOperators k m).obj (op U)) :
    X.restrictEnd k i D ∈ (X.differentialOperators k m).obj (op U') :=
  (X.differentialOperators k m).map i.op hD

/-- The order of an endomorphism of the structure sheaf on `V ⊆ U` is detected on any family of
open subsets covering `V`. -/
theorem endApp_mem_differentialOperators_of_le_iSup {m : ℕ} {U : X.Opens}
    (D : X.StructureEnd k U) (V : Over U) {ι : Type*} (W : ι → Over U) (hWV : ∀ i, W i ⟶ V)
    (hV : V.left ≤ ⨆ i, (W i).left)
    (hW : ∀ i, endApp D (W i) ∈
      TauCeti.differentialOperators k Γ(X, (W i).left) Γ(X, (W i).left) Γ(X, (W i).left) m) :
    endApp D V ∈ TauCeti.differentialOperators k Γ(X, V.left) Γ(X, V.left) Γ(X, V.left) m := by
  let r : ∀ i, Γ(X, V.left) →+* Γ(X, (W i).left) := fun i ↦ (X.presheaf.map (hWV i).left.op).hom
  let r' : ∀ i, Γ(X, V.left) →ₛₗ[r i] Γ(X, (W i).left) := fun i ↦
    { toFun := r i
      map_add' := map_add _
      map_smul' := map_mul _ }
  refine TauCeti.mem_differentialOperators_of_intertwining r r' r' (fun y hy ↦ ?_)
    (fun i x ↦ endApp_naturality D (hWV i) x) hW
  refine X.IsSheaf.section_ext (U := op V.left) (t := 0) fun x hx ↦ ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hV hx)
  exact ⟨(W i).left, (hWV i).left.le, hi, by rw [map_zero]; exact hy i⟩

variable (X k) in
/-- The order of an operator is local: `F_m D_X` is a subsheaf of the sheaf of endomorphisms of
the structure sheaf. -/
theorem isSheaf_differentialOperators (m : ℕ) :
    Presieve.IsSheaf (Opens.grothendieckTopology X) (X.differentialOperators k m).toFunctor := by
  refine (Subfunctor.isSheaf_iff _ (X.isSheaf_endPresheaf k)).2 fun U D hD V ↦ ?_
  -- the opens `W ⊆ V` on which `D` restricts to an operator of order at most `m` cover `V`
  let ι := {W : X.Opens // ∃ h : W ≤ V.left,
    (X.differentialOperators k m).sieveOfSection D (homOfLE (h.trans V.hom.le))}
  refine endApp_mem_differentialOperators_of_le_iSup D V
    (fun i : ι ↦ Over.mk (homOfLE (i.property.1.trans V.hom.le)))
    (fun i ↦ Over.homMk (homOfLE i.property.1)) (fun x hx ↦ ?_) fun i ↦ i.property.2 (Over.mk (𝟙 _))
  obtain ⟨W, f, hf, hxW⟩ := hD x (V.hom.le hx)
  exact Opens.mem_iSup.2 ⟨⟨W ⊓ V.left, inf_le_right,
    (X.differentialOperators k m).sieveOfSection D |>.downward_closed hf (homOfLE inf_le_left)⟩,
    hxW, hx⟩

/-! ### Multiplication by sections -/

/-- Restricting `f * g` along `W ⟶ V` over `U` multiplies the restrictions. -/
private theorem presheaf_map_mul_restrict {U : X.Opens} (f : Γ(X, U)) {V W : Over U} (j : W ⟶ V)
    (g : Γ(X, V.left)) :
    X.presheaf.map j.left.op (X.presheaf.map V.hom.op f * g) =
      X.presheaf.map W.hom.op f * X.presheaf.map j.left.op g := by
  rw [map_mul, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, Over.w j]

variable (X k) in
/-- Multiplication by a section `f` of `O_X` over `U`, as an endomorphism of the structure sheaf
restricted to `U`: on `V ⊆ U` it multiplies by the restriction of `f`. -/
noncomputable def toStructureEnd (U : X.Opens) : Γ(X, U) →+* X.StructureEnd k U where
  toFun f := StructureEnd.ofApp (fun V ↦ LinearMap.mulLeft k (X.presheaf.map V.hom.op f))
    fun j g ↦ presheaf_map_mul_restrict f j g
  map_one' := StructureEnd.ext fun _ ↦ LinearMap.ext fun g ↦
    (congrArg (· * g) (map_one _)).trans (one_mul g)
  map_mul' f f' := StructureEnd.ext fun _ ↦ LinearMap.ext fun g ↦
    (congrArg (· * g) (map_mul _ f f')).trans (mul_assoc _ _ g)
  map_zero' := StructureEnd.ext fun _ ↦ LinearMap.ext fun g ↦
    (congrArg (· * g) (map_zero _)).trans (zero_mul g)
  map_add' f f' := StructureEnd.ext fun _ ↦ LinearMap.ext fun g ↦
    (congrArg (· * g) (map_add _ f f')).trans (add_mul _ _ g)

@[simp]
theorem endApp_toStructureEnd {U : X.Opens} (f : Γ(X, U)) (V : Over U) (g : Γ(X, V.left)) :
    endApp (X.toStructureEnd k U f) V g = X.presheaf.map V.hom.op f * g :=
  (rfl)

theorem restrictEnd_toStructureEnd {U U' : X.Opens} (i : U' ⟶ U) (f : Γ(X, U)) :
    X.restrictEnd k i (X.toStructureEnd k U f) = X.toStructureEnd k U' (X.presheaf.map i.op f) := by
  ext V g
  simp only [endApp_restrictEnd, endApp_toStructureEnd, Over.map_obj_hom, op_comp,
    Functor.map_comp, CommRingCat.comp_apply]

theorem toStructureEnd_injective (U : X.Opens) : Function.Injective (X.toStructureEnd k U) := by
  intro f g h
  have h' := congr(endApp $h (Over.mk (𝟙 U)) 1)
  rw [endApp_toStructureEnd, endApp_toStructureEnd] at h'
  simpa using h'

theorem toStructureEnd_mem_differentialOperators_zero {U : X.Opens} (f : Γ(X, U)) :
    X.toStructureEnd k U f ∈ (X.differentialOperators k 0).obj (op U) :=
  fun _ ↦ TauCeti.mem_differentialOperators_zero_iff.2 fun _ _ ↦ by
    simp only [endApp_toStructureEnd, smul_eq_mul, mul_left_comm]

/-- The operators of order zero are exactly the multiplications by sections of `O_X`. -/
theorem mem_differentialOperators_zero_iff {U : X.Opens} {D : X.StructureEnd k U} :
    D ∈ (X.differentialOperators k 0).obj (op U) ↔ ∃ f, X.toStructureEnd k U f = D := by
  refine ⟨fun hD ↦ ⟨endApp D (Over.mk (𝟙 U)) 1, ?_⟩, ?_⟩
  · ext V g
    have h := endApp_naturality D (Over.homMk V.hom : V ⟶ Over.mk (𝟙 U)) 1
    simp only [map_one] at h
    have hV := TauCeti.mem_differentialOperators_zero_iff.1 (hD V) g 1
    rw [smul_eq_mul, mul_one] at hV
    rw [endApp_toStructureEnd, hV, smul_eq_mul, mul_comm]
    exact congr(g * $h)
  · rintro ⟨f, rfl⟩
    exact toStructureEnd_mem_differentialOperators_zero f

variable (X k) in
/-- `F_0 D_X = O_X`: multiplication identifies the structure sheaf with the sheaf of
differential operators of order zero. -/
noncomputable def differentialOperatorsZeroIso :
    X.presheaf ⋙ CategoryTheory.forget CommRingCat ≅ (X.differentialOperators k 0).toFunctor :=
  NatIso.ofComponents (fun U ↦ Equiv.toIso (Equiv.ofBijective
    (fun f ↦ ⟨X.toStructureEnd k U.unop f, toStructureEnd_mem_differentialOperators_zero f⟩)
    ⟨fun f g h ↦ toStructureEnd_injective (k := k) U.unop (congrArg Subtype.val h), fun D ↦
      (mem_differentialOperators_zero_iff.1 D.property).imp fun _ h ↦ Subtype.ext h⟩))
    fun i ↦ by
      ext f
      exact Subtype.ext (restrictEnd_toStructureEnd i.unop f).symm

-- The sources and targets of the components of `differentialOperatorsZeroIso` are spelled out in
-- their simp-normal form (without `Functor.comp_obj` and `Subfunctor.toFunctor_obj`), so that the
-- left-hand sides of the two lemmas below pass the `simpNF` linter.
/-- The operator of order zero corresponding to a section of `O_X` is multiplication by it. -/
@[simp]
theorem coe_differentialOperatorsZeroIso_hom_app_apply (U : X.Opensᵒᵖ) (f : Γ(X, U.unop)) :
    (ConcreteCategory.hom (C := Type u) (X := ToType (X.presheaf.obj U))
      (Y := (X.differentialOperators k 0).obj U)
      ((X.differentialOperatorsZeroIso k).hom.app U) f).val = X.toStructureEnd k U.unop f :=
  (rfl)

/-- The section of `O_X` corresponding to an operator of order zero is its value on `1`. -/
@[simp]
theorem differentialOperatorsZeroIso_inv_app_apply (U : X.Opensᵒᵖ)
    (D : (X.differentialOperators k 0).obj U) :
    ConcreteCategory.hom (C := Type u) (X := (X.differentialOperators k 0).obj U)
      (Y := ToType (X.presheaf.obj U)) ((X.differentialOperatorsZeroIso k).inv.app U) D =
      endApp D.val (Over.mk (𝟙 U.unop)) 1 := by
  obtain ⟨f, hf⟩ := mem_differentialOperators_zero_iff.1 D.property
  have hD : D = (X.differentialOperatorsZeroIso k).hom.app U f := Subtype.ext hf.symm
  subst hD
  rw [← types_comp_apply ((X.differentialOperatorsZeroIso k).hom.app U)
    ((X.differentialOperatorsZeroIso k).inv.app U), Iso.hom_inv_id_app,
    coe_differentialOperatorsZeroIso_hom_app_apply, endApp_toStructureEnd]
  simp

/-! ### The sheaf of rings of differential operators -/

/-- If `D` restricts to an operator of order at most `m` on `V ⊆ U`, it does so on every open
`V' ⊆ V`. -/
private theorem restrictEnd_mem_differentialOperators_of_le {m : ℕ} {U V V' : X.Opens}
    (hV : V ≤ U) (h : V' ≤ V) {D : X.StructureEnd k U}
    (hD : X.restrictEnd k (homOfLE hV) D ∈ (X.differentialOperators k m).obj (op V)) :
    X.restrictEnd k (homOfLE (h.trans hV)) D ∈ (X.differentialOperators k m).obj (op V') := by
  have := restrictEnd_mem_differentialOperators (homOfLE h) hD
  rw [restrictEnd_restrictEnd] at this
  exact this

variable (X k) in
/-- The sections over `U` of the sheaf of differential operators `D_X`: the endomorphisms of
the structure sheaf restricted to `U` that are locally of finite order, that is, every point of
`U` has an open neighbourhood `V ⊆ U` on which the endomorphism has order at most some `m`.
They form a subring under composition. -/
noncomputable def differentialOperatorsSubring (U : X.Opens) : Subring (X.StructureEnd k U) where
  carrier := {D | ∀ x ∈ U, ∃ (V : X.Opens) (h : V ≤ U) (m : ℕ),
    x ∈ V ∧ X.restrictEnd k (homOfLE h) D ∈ (X.differentialOperators k m).obj (op V)}
  one_mem' x hx := ⟨U, le_rfl, 0, hx, by
    rw [map_one]; exact one_mem_differentialOperators 0 U⟩
  mul_mem' {D E} hD hE x hx := by
    obtain ⟨V, hV, p, hxV, hpD⟩ := hD x hx
    obtain ⟨W, hW, q, hxW, hqE⟩ := hE x hx
    refine ⟨V ⊓ W, inf_le_left.trans hV, p + q, ⟨hxV, hxW⟩, ?_⟩
    rw [map_mul]
    exact mul_mem_differentialOperators (restrictEnd_mem_differentialOperators_of_le hV
      inf_le_left hpD) (restrictEnd_mem_differentialOperators_of_le hW inf_le_right hqE)
  zero_mem' x hx := ⟨U, le_rfl, 0, hx, by
    rw [map_zero]; exact zero_mem_differentialOperators 0 U⟩
  add_mem' {D E} hD hE x hx := by
    obtain ⟨V, hV, p, hxV, hpD⟩ := hD x hx
    obtain ⟨W, hW, q, hxW, hqE⟩ := hE x hx
    refine ⟨V ⊓ W, inf_le_left.trans hV, max p q, ⟨hxV, hxW⟩, ?_⟩
    rw [map_add]
    exact add_mem_differentialOperators
      (differentialOperators_mono (le_max_left p q) _
        (restrictEnd_mem_differentialOperators_of_le hV inf_le_left hpD))
      (differentialOperators_mono (le_max_right p q) _
        (restrictEnd_mem_differentialOperators_of_le hW inf_le_right hqE))
  neg_mem' {D} hD x hx := by
    obtain ⟨V, hV, m, hxV, hD⟩ := hD x hx
    exact ⟨V, hV, m, hxV, by rw [map_neg]; exact neg_mem_differentialOperators hD⟩

theorem mem_differentialOperatorsSubring_iff {U : X.Opens} {D : X.StructureEnd k U} :
    D ∈ X.differentialOperatorsSubring k U ↔ ∀ x ∈ U, ∃ (V : X.Opens) (h : V ≤ U) (m : ℕ),
      x ∈ V ∧ X.restrictEnd k (homOfLE h) D ∈ (X.differentialOperators k m).obj (op V) :=
  Iff.rfl

/-- An operator of order at most `m` is a differential operator. -/
theorem mem_differentialOperatorsSubring_of_mem {m : ℕ} {U : X.Opens} {D : X.StructureEnd k U}
    (hD : D ∈ (X.differentialOperators k m).obj (op U)) : D ∈ X.differentialOperatorsSubring k U :=
  fun x hx ↦ ⟨U, le_rfl, m, hx, by simpa using hD⟩

theorem restrictEnd_mem_differentialOperatorsSubring {U U' : X.Opens} (i : U' ⟶ U)
    {D : X.StructureEnd k U} (hD : D ∈ X.differentialOperatorsSubring k U) :
    X.restrictEnd k i D ∈ X.differentialOperatorsSubring k U' := by
  intro x hx
  obtain ⟨V, hV, m, hxV, hD⟩ := hD x (i.le hx)
  refine ⟨V ⊓ U', inf_le_right, m, ⟨hxV, hx⟩, ?_⟩
  rw [restrictEnd_restrictEnd]
  exact restrictEnd_mem_differentialOperators_of_le hV (inf_le_left : V ⊓ U' ≤ V) hD

variable (X k) in
/-- The sheaf of differential operators `D_X` as a presheaf of types, the subpresheaf of
`X.endPresheaf k` cut out by `differentialOperatorsSubring`. -/
private noncomputable def differentialOperatorsSubfunctor : Subfunctor (X.endPresheaf k) where
  obj U := (X.differentialOperatorsSubring k U.unop : Set (X.StructureEnd k U.unop))
  map i _ hD := restrictEnd_mem_differentialOperatorsSubring i.unop hD

private theorem isSheaf_differentialOperatorsSubfunctor :
    Presieve.IsSheaf (Opens.grothendieckTopology X)
      (X.differentialOperatorsSubfunctor k).toFunctor := by
  refine (Subfunctor.isSheaf_iff _ (X.isSheaf_endPresheaf k)).2 fun U D hD x hx ↦ ?_
  obtain ⟨W, f, hf, hxW⟩ := hD x hx
  obtain ⟨V, hV, m, hxV, hDV⟩ := hf x hxW
  refine ⟨V, hV.trans f.le, m, hxV, ?_⟩
  exact (congrArg (· ∈ (X.differentialOperators k m).obj (op V))
    (restrictEnd_restrictEnd f (homOfLE hV) D)).mp hDV

variable (X k) in
/-- The presheaf of rings of differential operators on `X`, with multiplication given by
composition. -/
@[expose] noncomputable def presheafOfDifferentialOperators : X.Opensᵒᵖ ⥤ RingCat.{u} where
  obj U := RingCat.of (X.differentialOperatorsSubring k U.unop)
  map i := RingCat.ofHom ((X.restrictEnd k i.unop).restrict _ _
    fun _ ↦ restrictEnd_mem_differentialOperatorsSubring i.unop)
  map_id _ := RingCat.hom_ext (RingHom.ext fun D ↦ Subtype.ext (restrictEnd_id D.val))
  map_comp f g := RingCat.hom_ext
    (RingHom.ext fun D ↦ Subtype.ext (restrictEnd_restrictEnd f.unop g.unop D.val).symm)

@[simp]
theorem coe_presheafOfDifferentialOperators_map_apply {U U' : X.Opensᵒᵖ} (i : U ⟶ U')
    (D : (X.presheafOfDifferentialOperators k).obj U) :
    ((X.presheafOfDifferentialOperators k).map i D).val = X.restrictEnd k i.unop D.val :=
  (rfl)

variable (X k) in
/-- The presheaf of differential operators is a sheaf: being locally of finite order is a local
condition. -/
theorem isSheaf_presheafOfDifferentialOperators :
    TopCat.Presheaf.IsSheaf (X.presheafOfDifferentialOperators k) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp (CategoryTheory.forget RingCat)]
  refine TopCat.Presheaf.isSheaf_of_iso (NatIso.ofComponents (fun U ↦ Iso.refl _) fun _ ↦ rfl)
    ((isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_differentialOperatorsSubfunctor (k := k)))

variable (X k) in
/-- The sheaf of rings `D_X` of differential operators on a scheme `X` over `Spec k`. -/
noncomputable def sheafOfDifferentialOperators : TopCat.Sheaf RingCat.{u} X :=
  ⟨X.presheafOfDifferentialOperators k, X.isSheaf_presheafOfDifferentialOperators k⟩

variable (X k) in
/-- The underlying presheaf of the sheaf of differential operators. -/
@[simp]
theorem sheafOfDifferentialOperators_obj :
    (X.sheafOfDifferentialOperators k).obj = X.presheafOfDifferentialOperators k :=
  (rfl)

variable (X k) in
/-- The ring map `O_X → D_X` sending a section to multiplication by it. -/
noncomputable def toPresheafOfDifferentialOperators :
    X.presheaf ⋙ forget₂ CommRingCat RingCat ⟶ X.presheafOfDifferentialOperators k where
  app U := RingCat.ofHom ((X.toStructureEnd k U.unop).codRestrict _ fun f ↦
    mem_differentialOperatorsSubring_of_mem (toStructureEnd_mem_differentialOperators_zero f))
  naturality U U' i := by
    ext f
    exact Subtype.ext (restrictEnd_toStructureEnd i.unop f).symm

theorem coe_toPresheafOfDifferentialOperators_app_apply (U : X.Opensᵒᵖ) (f : Γ(X, U.unop)) :
    ((X.toPresheafOfDifferentialOperators k).app U f).val = X.toStructureEnd k U.unop f :=
  (rfl)

/-- On the empty scheme every endomorphism of the structure sheaf is zero. -/
instance [IsEmpty X] (U : X.Opens) : Subsingleton (X.StructureEnd k U) :=
  ⟨fun _ _ ↦ StructureEnd.ext fun _ ↦ LinearMap.ext fun _ ↦ Subsingleton.elim _ _⟩

/-- On the empty scheme the sheaf of differential operators is the zero sheaf of rings. -/
instance [IsEmpty X] (U : X.Opensᵒᵖ) :
    Subsingleton ((X.presheafOfDifferentialOperators k).obj U) :=
  inferInstanceAs (Subsingleton (X.differentialOperatorsSubring k U.unop))

end AlgebraicGeometry.Scheme
