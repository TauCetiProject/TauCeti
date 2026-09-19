/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Germ
public import TauCeti.AlgebraicGeometry.Cohomology.Flasque
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# The sheaf of principal parts of a Weil divisor

Let `X` be a Noetherian integral scheme whose local rings at codimension-one points are discrete
valuation rings, and let `D` be a Weil divisor on `X`. This file builds the sheaf of principal
parts of `D` concretely, as the direct sum of the skyscraper sheaves `K(X) / 𝒪_X(D)_x` at the
codimension-one points `x`: its sections over `U` are the finitely supported families of principal
parts at the codimension-one points of `U`. When the codimension-one points are closed, as on a
curve, it is the quotient `𝒦_X / 𝒪_X(D)`, that is, it sits in a short exact sequence

`0 ⟶ 𝒪_X(D) ⟶ 𝒦_X ⟶ 𝒦_X / 𝒪_X(D) ⟶ 0`

of `𝒪_X`-modules whose last two terms are flasque. This is the flasque resolution of `𝒪_X(D)`
through which its cohomology on a curve is computed.

## Main declarations

* `SchemeWeilDivisor.stalkSubmodule D x`, the stalk `𝒪_X(D)_x ⊆ K(X)` at a codimension-one
  point, and `SchemeWeilDivisor.PrincipalPart D x`, the quotient `K(X) / 𝒪_X(D)_x`;
* `SchemeWeilDivisor.principalParts D`, the sheaf of principal parts, together with the
  description `principalParts_presheaf_map_apply` of its restriction maps and the instance saying
  that it is flasque;
* `SchemeWeilDivisor.toPrincipalParts D : 𝒦_X ⟶ principalParts D`, taking a rational function to
  its principal parts `SchemeWeilDivisor.principalPartAt`, with kernel `𝒪_X(D)`
  (`toPrincipalParts_app_eq_zero_iff`, `isLimitKernelForkSheafι`);
* `SchemeWeilDivisor.exists_toPrincipalParts_app_eq` and `SchemeWeilDivisor.epi_toPrincipalParts`:
  if the codimension-one points are closed, principal parts can be prescribed locally, so
  `toPrincipalParts D` is an epimorphism;
* `SchemeWeilDivisor.principalPartsShortComplex_shortExact`, the resulting short exact sequence.

No formalization is vendored. The sheaf `𝒪_X(D)` and its inclusion into `𝒦_X` are
`TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/Sheaf.lean`, the finiteness of the points at which a
rational function violates the order bound is `SchemeWeilDivisor.finite_setOf_ord_lt`, the sheaf
condition is checked through Mathlib's `TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing`, and
surjectivity through `TopCat.Sheaf.isLocallySurjective_iff_epi`.

## References

* R. Hartshorne, *Algebraic Geometry*, II, Exercise 1.21 (the sheaf `𝒦 / 𝒪` on a curve as a sum
  of skyscraper sheaves).
* J.-P. Serre, *Algebraic Groups and Class Fields*, Chapter II, §5 (répartitions and the
  cohomology of `𝒪_X(D)`).
-/

public section

open CategoryTheory Limits Order TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X : Scheme.{u}}

noncomputable section

/-- The germs at the codimension-one points of `U` of a function on `U`. -/
def germs (U : X.Opens) :
    Γ(X, U) →+* ∀ x : {x : CodimensionOnePoint X // (x : X) ∈ U}, X.presheaf.stalk (x.1 : X) :=
  RingHom.pi fun x ↦ (X.presheaf.germ U x.1 x.2).hom

@[simp]
lemma germs_apply (U : X.Opens) (r : Γ(X, U)) (x : {x : CodimensionOnePoint X // (x : X) ∈ U}) :
    germs U r x = X.presheaf.germ U x.1 x.2 r :=
  (rfl)

variable [IsIntegral X]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]

section LocallyNoetherian

variable [IsLocallyNoetherian X]

/-- The stalk of `𝒪_X(D)` at a codimension-one point `x`, as a submodule of the function field
over the local ring at `x`: the rational functions which vanish or have order at least `-D(x)`
at `x`. -/
def stalkSubmodule (D : SchemeWeilDivisor X) (x : CodimensionOnePoint X) :
    Submodule (X.presheaf.stalk (x : X)) X.functionField where
  carrier := {f | f = 0 ∨ -WeilDivisor.coeff D x ≤ X.ord f x}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro f g hf hg
    rcases hf with rfl | hf
    · simpa using hg
    rcases hg with rfl | hg
    · simpa using Or.inr hf
    by_cases h : f + g = 0
    · exact Or.inl h
    · exact Or.inr <| le_trans (le_min hf hg) (Scheme.ord_add h)
  smul_mem' := by
    intro a f hf
    obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq a
    have : Nonempty U := ⟨⟨x, hxU⟩⟩
    simp only [Set.mem_ofPred_eq, Scheme.germ_smul_functionField]
    rcases eq_or_ne r 0 with rfl | hr
    · exact Or.inl (zero_smul _ f)
    rcases hf with rfl | hf
    · exact Or.inl (smul_zero r)
    · exact Or.inr (hf.trans (Scheme.ord_le_smul hxU hr f))

@[simp]
lemma mem_stalkSubmodule {D : SchemeWeilDivisor X} {x : CodimensionOnePoint X}
    {f : X.functionField} :
    f ∈ stalkSubmodule D x ↔ f = 0 ∨ -WeilDivisor.coeff D x ≤ X.ord f x :=
  Iff.rfl

/-- The module of principal parts of `D` at a codimension-one point `x`: the quotient of the
function field by the stalk of `𝒪_X(D)` at `x`. -/
abbrev PrincipalPart (D : SchemeWeilDivisor X) (x : CodimensionOnePoint X) : Type u :=
  X.functionField ⧸ stalkSubmodule D x

/-- The finitely supported families of principal parts of `D` at the codimension-one points of
`U`, as a module over the product of the local rings at these points. -/
def principalPartsSubmodule (D : SchemeWeilDivisor X) (U : X.Opens) :
    Submodule (∀ x : {x : CodimensionOnePoint X // (x : X) ∈ U}, X.presheaf.stalk (x.1 : X))
      (∀ x : {x : CodimensionOnePoint X // (x : X) ∈ U}, PrincipalPart D x.1) where
  carrier := {s | {x | s x ≠ 0}.Finite}
  zero_mem' := by simp
  add_mem' {s t} hs ht := (hs.union ht).subset fun x hx ↦ by
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h hx
    exact hx (by rw [Pi.add_apply, h.1, h.2, add_zero])
  smul_mem' a s hs := hs.subset fun x hx h ↦ hx (by rw [Pi.smul_apply', h, smul_zero])

@[simp]
lemma mem_principalPartsSubmodule {D : SchemeWeilDivisor X} {U : X.Opens}
    {s : ∀ x : {x : CodimensionOnePoint X // (x : X) ∈ U}, PrincipalPart D x.1} :
    s ∈ principalPartsSubmodule D U ↔ {x | s x ≠ 0}.Finite :=
  Iff.rfl

/-- Restriction of a finitely supported family of principal parts to a smaller open subset. -/
def principalPartsRestrict (D : SchemeWeilDivisor X) {U V : X.Opens} (i : V ⟶ U) :
    principalPartsSubmodule D U →+ principalPartsSubmodule D V where
  toFun s := ⟨fun y ↦ s.1 ⟨y.1, i.le y.2⟩, by
    refine ((mem_principalPartsSubmodule.mp s.2).preimage
      (f := fun y : {x : CodimensionOnePoint X // (x : X) ∈ V} ↦
        (⟨y.1, i.le y.2⟩ : {x : CodimensionOnePoint X // (x : X) ∈ U})) ?_).subset fun y hy ↦ hy
    intro a _ b _ h
    exact Subtype.ext (congrArg Subtype.val h :)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
lemma principalPartsRestrict_apply (D : SchemeWeilDivisor X) {U V : X.Opens} (i : V ⟶ U)
    (s : principalPartsSubmodule D U) (y : {x : CodimensionOnePoint X // (x : X) ∈ V}) :
    (principalPartsRestrict D i s).1 y = s.1 ⟨y.1, i.le y.2⟩ :=
  (rfl)

/-- The `Γ(X, U)`-module of finitely supported families of principal parts of `D` at the
codimension-one points of `U`, the ring acting through its germs. -/
abbrev principalPartsObj (D : SchemeWeilDivisor X) (U : X.Opens) :
    ModuleCat.{u} (X.ringCatSheaf.obj.obj (op U)) :=
  (ModuleCat.restrictScalars (germs U)).obj (ModuleCat.of _ (principalPartsSubmodule D U))

/-- A function on `U` acts on a family of principal parts through its germs. -/
lemma principalPartsObj_smul_apply (D : SchemeWeilDivisor X) (U : X.Opens) (r : Γ(X, U))
    (s : principalPartsObj D U) (x : {x : CodimensionOnePoint X // (x : X) ∈ U}) :
    (r • s : principalPartsSubmodule D U).1 x = X.presheaf.germ U x.1 x.2 r • s.1 x :=
  (rfl)

/-- The presheaf of `𝒪_X`-modules of principal parts of `D`. -/
@[expose]
def principalPartsPresheaf (D : SchemeWeilDivisor X) :
    PresheafOfModules X.ringCatSheaf.obj where
  obj U := principalPartsObj D U.unop
  map {U V} i := ModuleCat.semilinearMapAddEquiv (X.ringCatSheaf.obj.map i).hom
    (principalPartsObj D U.unop) (principalPartsObj D V.unop)
    { toFun := principalPartsRestrict D i.unop
      map_add' := map_add _
      map_smul' := by
        intro r s
        apply Subtype.ext
        funext y
        -- Both actions are multiplication by a germ at `y`, of `r` and of its restriction.
        exact congrArg (· • s.1 ⟨y.1, i.unop.le y.2⟩)
          (X.presheaf.germ_res_apply i.unop y.1 y.2 r).symm }

end LocallyNoetherian

section Noetherian

variable [IsNoetherian X]

/-- On a Noetherian scheme, principal parts form a sheaf: compatible finitely supported families
glue pointwise, and the glued family is finitely supported because the union of the open subsets
is quasi-compact. -/
theorem isSheaf_principalPartsPresheaf (D : SchemeWeilDivisor X) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (principalPartsPresheaf D).presheaf := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr ?_
  intro ι U sf hsf
  let sf' : ∀ i, principalPartsSubmodule D (U i) := sf
  -- The restriction maps are `principalPartsRestrict`, so compatibility and gluing are
  -- pointwise conditions. Two members of the family agree at every point of the intersection
  -- of their domains.
  have hagree : ∀ (i j : ι) (x : CodimensionOnePoint X) (hi : (x : X) ∈ U i)
      (hj : (x : X) ∈ U j), (sf' i).1 ⟨x, hi⟩ = (sf' j).1 ⟨x, hj⟩ := by
    intro i j x hi hj
    exact congrArg (fun t : principalPartsSubmodule D (U i ⊓ U j) ↦ t.1 ⟨x, hi, hj⟩) (hsf i j)
  have hmem : ∀ x : {x : CodimensionOnePoint X // (x : X) ∈ iSup U}, ∃ i, (x.1 : X) ∈ U i :=
    fun x ↦ Opens.mem_iSup.mp x.2
  let g : ∀ x : {x : CodimensionOnePoint X // (x : X) ∈ iSup U}, PrincipalPart D x.1 :=
    fun x ↦ (sf' (hmem x).choose).1 ⟨x.1, (hmem x).choose_spec⟩
  have hg : ∀ (x : {x : CodimensionOnePoint X // (x : X) ∈ iSup U}) (i : ι)
      (hi : (x.1 : X) ∈ U i), g x = (sf' i).1 ⟨x.1, hi⟩ :=
    fun x i hi ↦ hagree _ _ _ _ _
  have hfin : {x | g x ≠ 0}.Finite := by
    obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact ((iSup U : X.Opens) : Set X)).elim_finite_subcover
      (fun i ↦ (U i : Set X)) (fun i ↦ (U i).isOpen) (by simp [Opens.coe_iSup])
    refine (t.finite_toSet.biUnion fun i _ ↦
      ((mem_principalPartsSubmodule.mp (sf' i).2).image
        fun y ↦ (⟨y.1, Opens.mem_iSup.mpr ⟨i, y.2⟩⟩ :
          {x : CodimensionOnePoint X // (x : X) ∈ iSup U}))).subset ?_
    intro x hx
    obtain ⟨i, hit, hi⟩ := Set.mem_iUnion₂.mp (ht x.2)
    refine Set.mem_biUnion hit ⟨⟨x.1, hi⟩, ?_, rfl⟩
    rw [Set.mem_ofPred_eq, ← hg x i hi]
    exact hx
  refine ⟨(⟨g, hfin⟩ : principalPartsSubmodule D (iSup U)), ?_, ?_⟩
  · intro i
    apply Subtype.ext
    funext y
    exact hg ⟨y.1, _⟩ i y.2
  · intro s hs
    apply Subtype.ext
    funext x
    obtain ⟨i, hi⟩ := hmem x
    refine Eq.trans ?_ (hg x i hi).symm
    exact congrArg (fun t : principalPartsSubmodule D (U i) ↦ t.1 ⟨x.1, hi⟩) (hs i)

/-- The sheaf of `𝒪_X`-modules of principal parts of a Weil divisor `D` on a Noetherian integral
scheme: its sections over `U` are the finitely supported families of principal parts
`K(X) / 𝒪_X(D)_x` at the codimension-one points `x` of `U`. When the codimension-one points are
closed it is the quotient `𝒦_X / 𝒪_X(D)`, by `principalPartsShortComplex_shortExact`. -/
@[expose]
def principalParts (D : SchemeWeilDivisor X) : X.Modules :=
  ⟨principalPartsPresheaf D, isSheaf_principalPartsPresheaf D⟩

/-- The restriction maps of the sheaf of principal parts forget the points outside the smaller
open subset. -/
@[simp]
lemma principalParts_presheaf_map_apply (D : SchemeWeilDivisor X) {U V : X.Opens} (i : V ⟶ U)
    (s : principalPartsSubmodule D U) (y : {x : CodimensionOnePoint X // (x : X) ∈ V}) :
    ((principalParts D).presheaf.map i.op s : principalPartsSubmodule D V).1 y =
      s.1 ⟨y.1, i.le y.2⟩ :=
  (rfl)

/-- The sheaf of principal parts is flasque: a finitely supported family on a smaller open subset
extends by zero. -/
instance (D : SchemeWeilDivisor X) : (principalParts D).presheaf.IsFlasque where
  epi {U V} i := by
    classical
    rw [AddCommGrpCat.epi_iff_surjective]
    intro t
    let t' : principalPartsSubmodule D V.unop := t
    let g : ∀ x : {x : CodimensionOnePoint X // (x : X) ∈ U.unop}, PrincipalPart D x.1 :=
      fun x ↦ if h : (x.1 : X) ∈ V.unop then t'.1 ⟨x.1, h⟩ else 0
    have hfin : {x | g x ≠ 0}.Finite := by
      refine ((mem_principalPartsSubmodule.mp t'.2).image
        fun y ↦ (⟨y.1, i.unop.le y.2⟩ : {x : CodimensionOnePoint X // (x : X) ∈ U.unop})).subset ?_
      intro x hx
      by_cases h : (x.1 : X) ∈ V.unop
      · refine ⟨⟨x.1, h⟩, ?_, rfl⟩
        simpa [g, h] using hx
      · exact absurd (by simp [g, h]) hx
    refine ⟨(⟨g, hfin⟩ : principalPartsSubmodule D U.unop), ?_⟩
    -- The restriction map is `principalPartsRestrict`, evaluation at the points of `V`.
    apply Subtype.ext
    funext y
    exact dite_eq_left y.2

/-- The principal part at a codimension-one point `x` of `U` of a section of `𝒦_X` over `U`. -/
def principalPartAt (D : SchemeWeilDivisor X) {U : X.Opens} (s : Γ(Scheme.rationalFunctions X, U))
    (x : {x : CodimensionOnePoint X // (x : X) ∈ U}) : PrincipalPart D x.1 :=
  haveI : Nonempty U := ⟨⟨x.1, x.2⟩⟩
  Submodule.Quotient.mk (Scheme.rationalFunctionsEquiv U s)

/-- Over a nonempty open subset, the principal part at `x` is the class of the rational function
in `K(X) / 𝒪_X(D)_x`. -/
lemma principalPartAt_eq (D : SchemeWeilDivisor X) {U : X.Opens} [Nonempty U]
    (s : Γ(Scheme.rationalFunctions X, U)) (x : {x : CodimensionOnePoint X // (x : X) ∈ U}) :
    principalPartAt D s x = Submodule.Quotient.mk (Scheme.rationalFunctionsEquiv U s) :=
  (rfl)

/-- The principal part of a section of `𝒦_X` at a codimension-one point vanishes exactly when the
rational function lies in the stalk of `𝒪_X(D)` there. -/
lemma principalPartAt_eq_zero_iff (D : SchemeWeilDivisor X) {U : X.Opens}
    (s : Γ(Scheme.rationalFunctions X, U)) (x : {x : CodimensionOnePoint X // (x : X) ∈ U}) :
    principalPartAt D s x = 0 ↔
      haveI : Nonempty U := ⟨⟨x.1, x.2⟩⟩
      Scheme.rationalFunctionsEquiv U s ∈ stalkSubmodule D x.1 :=
  Submodule.Quotient.mk_eq_zero _

/-- A fixed rational function has a nonzero principal part at finitely many codimension-one
points only. -/
lemma finite_setOf_mk_ne_zero (D : SchemeWeilDivisor X) (f : X.functionField) :
    {x : CodimensionOnePoint X | (Submodule.Quotient.mk f : PrincipalPart D x) ≠ 0}.Finite := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · refine (finite_setOf_ord_lt D hf).subset fun x hx ↦ ?_
    rw [Set.mem_ofPred_eq, ne_eq, Submodule.Quotient.mk_eq_zero, mem_stalkSubmodule, not_or,
      not_le] at hx
    exact hx.2

/-- The principal parts of a section of `𝒦_X` over `U` at the codimension-one points of `U` are
finitely supported: a nonzero rational function violates the order bound imposed by `D` at
finitely many codimension-one points only. -/
lemma finite_setOf_principalPartAt_ne_zero (D : SchemeWeilDivisor X) {U : X.Opens}
    (s : Γ(Scheme.rationalFunctions X, U)) : {x | principalPartAt D s x ≠ 0}.Finite := by
  rcases isEmpty_or_nonempty U with hU | hU
  · have : IsEmpty {x : CodimensionOnePoint X // (x : X) ∈ U} :=
      ⟨fun x ↦ hU.false ⟨x.1, x.2⟩⟩
    exact Set.toFinite _
  refine ((finite_setOf_mk_ne_zero D (Scheme.rationalFunctionsEquiv U s)).preimage
    Subtype.val_injective.injOn).subset fun x hx ↦ ?_
  rwa [Set.mem_ofPred_eq, principalPartAt_eq] at hx

/-- The principal parts of the sections of `𝒦_X` over `U`. -/
def toPrincipalPartsApp (D : SchemeWeilDivisor X) (U : X.Opens) :
    Γ(Scheme.rationalFunctions X, U) →+ principalPartsSubmodule D U where
  toFun s := ⟨principalPartAt D s, finite_setOf_principalPartAt_ne_zero D s⟩
  map_zero' := by
    apply Subtype.ext
    funext x
    have : Nonempty U := ⟨⟨x.1, x.2⟩⟩
    simp [principalPartAt_eq]
  map_add' s t := by
    apply Subtype.ext
    funext x
    have : Nonempty U := ⟨⟨x.1, x.2⟩⟩
    simp [principalPartAt_eq]

/-- The principal parts of `r • s` are those of `s` multiplied by the germs of `r`. -/
lemma principalPartAt_smul (D : SchemeWeilDivisor X) {U : X.Opens} (r : Γ(X, U))
    (s : Γ(Scheme.rationalFunctions X, U)) (x : {x : CodimensionOnePoint X // (x : X) ∈ U}) :
    principalPartAt D (r • s) x = X.presheaf.germ U x.1 x.2 r • principalPartAt D s x := by
  have : Nonempty U := ⟨⟨x.1, x.2⟩⟩
  rw [principalPartAt_eq, principalPartAt_eq, map_smul, ← Submodule.Quotient.mk_smul,
    Scheme.germ_smul_functionField]

/-- Principal parts commute with restriction. -/
lemma principalPartAt_map (D : SchemeWeilDivisor X) {U V : X.Opens} (i : V ⟶ U)
    (s : Γ(Scheme.rationalFunctions X, U)) (y : {x : CodimensionOnePoint X // (x : X) ∈ V}) :
    principalPartAt D ((Scheme.rationalFunctions X).presheaf.map i.op s) y =
      principalPartAt D s ⟨y.1, i.le y.2⟩ := by
  have : Nonempty V := ⟨⟨y.1, y.2⟩⟩
  have : Nonempty U := ⟨⟨y.1, i.le y.2⟩⟩
  rw [principalPartAt_eq, principalPartAt_eq, Scheme.rationalFunctionsEquiv_map]

/-- The morphism from `𝒦_X` to the sheaf of principal parts of `D`, taking a rational function to
its principal parts at the codimension-one points. -/
def toPrincipalParts (D : SchemeWeilDivisor X) :
    Scheme.rationalFunctions X ⟶ principalParts D :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (toPrincipalPartsApp D U.unop)
      naturality {U V} i := by
        ext s
        apply Subtype.ext
        funext y
        exact principalPartAt_map D i.unop s y }
    (by
      intro U r s
      apply Subtype.ext
      funext x
      exact principalPartAt_smul D r s x)⟩

@[simp]
lemma toPrincipalParts_app_apply (D : SchemeWeilDivisor X) (U : X.Opens)
    (s : Γ(Scheme.rationalFunctions X, U)) (x : {x : CodimensionOnePoint X // (x : X) ∈ U}) :
    (Scheme.Modules.Hom.app (toPrincipalParts D) U s : principalPartsSubmodule D U).1 x =
      principalPartAt D s x :=
  (rfl)

/-- **The kernel of `toPrincipalParts D` is `𝒪_X(D)`**, on sections: a rational function on `U`
has vanishing principal parts at every codimension-one point of `U` exactly when it is a section
of `𝒪_X(D)` over `U`. -/
lemma toPrincipalParts_app_eq_zero_iff (D : SchemeWeilDivisor X) (U : X.Opens)
    (s : Γ(Scheme.rationalFunctions X, U)) :
    Scheme.Modules.Hom.app (toPrincipalParts D) U s = 0 ↔ s ∈ sections D U := by
  rw [mem_sections]
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · have := congrArg (fun t : principalPartsSubmodule D U ↦ t.1 ⟨x, hx⟩) h
    exact (principalPartAt_eq_zero_iff D s ⟨x, hx⟩).mp this
  · apply Subtype.ext
    funext x
    exact (principalPartAt_eq_zero_iff D s x).mpr (h x.1 x.2)

@[reassoc (attr := simp)]
lemma sheafι_toPrincipalParts (D : SchemeWeilDivisor X) :
    sheafι D ≫ toPrincipalParts D = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext t
  exact (toPrincipalParts_app_eq_zero_iff D U _).mpr (sheafι_app_mem D U t)

/-- The sequence `𝒪_X(D) ⟶ 𝒦_X ⟶ principalParts D` of `𝒪_X`-modules. It is exact in the middle
(`principalPartsShortComplex_exact`), and short exact when the codimension-one points are closed
(`principalPartsShortComplex_shortExact`). -/
@[expose]
def principalPartsShortComplex (D : SchemeWeilDivisor X) : ShortComplex X.Modules :=
  ShortComplex.mk (sheafι D) (toPrincipalParts D) (sheafι_toPrincipalParts D)

/-- `𝒪_X(D)` is the kernel of `toPrincipalParts D : 𝒦_X ⟶ principalParts D`. -/
def isLimitKernelForkSheafι (D : SchemeWeilDivisor X) :
    IsLimit (KernelFork.ofι (sheafι D) (sheafι_toPrincipalParts D)) :=
  KernelFork.IsLimit.ofι _ _
    (fun φ hφ ↦ sheafLift D φ fun U s ↦ (toPrincipalParts_app_eq_zero_iff D U _).mp <| by
      simpa using ConcreteCategory.congr_hom
        (congrArg (fun η ↦ Scheme.Modules.Hom.app η U) hφ) s)
    (fun φ hφ ↦ sheafLift_ι D φ _)
    (fun φ hφ m hm ↦ by
      rw [← cancel_mono (sheafι D), sheafLift_ι]
      exact hm)

/-- The sequence `𝒪_X(D) ⟶ 𝒦_X ⟶ principalParts D` is exact in the middle. -/
lemma principalPartsShortComplex_exact (D : SchemeWeilDivisor X) :
    (principalPartsShortComplex D).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (isLimitKernelForkSheafι D)

section ClosedPoints

variable (hclosed : ∀ x : CodimensionOnePoint X, IsClosed ({(x : X)} : Set X))

include hclosed

/-- **Principal parts can be prescribed locally.** If the codimension-one points are closed, a
finitely supported family of principal parts on `U` is, near any point `y` of `U`, the family of
principal parts of a single rational function: take a rational function with the prescribed
principal part at `y`, and delete the finitely many other points at which the family or that
function has a nonzero principal part. -/
theorem exists_toPrincipalParts_app_eq (D : SchemeWeilDivisor X) {U : X.Opens}
    (t : principalPartsSubmodule D U) {y : X} (hy : y ∈ U) :
    ∃ (V : X.Opens) (i : V ⟶ U), y ∈ V ∧ ∃ s : Γ(Scheme.rationalFunctions X, V),
      Scheme.Modules.Hom.app (toPrincipalParts D) V s = (principalParts D).presheaf.map i.op t := by
  -- A rational function with the prescribed principal part at `y`, if `y` has codimension one.
  obtain ⟨f, hf⟩ : ∃ f : X.functionField, ∀ h : coheight y = 1,
      Submodule.Quotient.mk f = t.1 ⟨⟨y, h⟩, hy⟩ := by
    by_cases h : coheight y = 1
    · obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective _ (t.1 ⟨⟨y, h⟩, hy⟩)
      exact ⟨f, fun _ ↦ hf⟩
    · exact ⟨0, fun h' ↦ absurd h' h⟩
  have hfy : ∀ (w : CodimensionOnePoint X) (hw : (w : X) = y) (hwU : (w : X) ∈ U),
      Submodule.Quotient.mk f = t.1 ⟨w, hwU⟩ := by
    rintro ⟨w, hwc⟩ rfl hwU
    exact hf hwc
  -- The codimension-one points other than `y` at which `t` or `f` has a nonzero principal part.
  let E : Set (CodimensionOnePoint X) := {x | (x : X) ≠ y ∧
    ((∃ hx : (x : X) ∈ U, t.1 ⟨x, hx⟩ ≠ 0) ∨ (Submodule.Quotient.mk f : PrincipalPart D x) ≠ 0)}
  have hE : E.Finite := by
    refine (((mem_principalPartsSubmodule.mp t.2).image Subtype.val).union
      (finite_setOf_mk_ne_zero D f)).subset ?_
    rintro x ⟨-, ⟨hx, hxt⟩ | hxf⟩
    · exact Or.inl ⟨⟨x, hx⟩, hxt, rfl⟩
    · exact Or.inr hxf
  have hZ : IsClosed (⋃ x ∈ E, ({(x : X)} : Set X)) := hE.isClosed_biUnion fun x _ ↦ hclosed x
  let V : X.Opens := U ⊓ ⟨(⋃ x ∈ E, ({(x : X)} : Set X))ᶜ, hZ.isOpen_compl⟩
  have hyV : y ∈ V := by
    refine ⟨hy, fun h ↦ ?_⟩
    obtain ⟨x, hx, hxy⟩ := Set.mem_iUnion₂.mp h
    exact hx.1 (Set.mem_singleton_iff.mp hxy).symm
  have : Nonempty V := ⟨⟨y, hyV⟩⟩
  refine ⟨V, homOfLE inf_le_left, hyV, (Scheme.rationalFunctionsEquiv V).symm f, ?_⟩
  apply Subtype.ext
  funext z
  rw [toPrincipalParts_app_apply, principalPartAt_eq, LinearEquiv.apply_symm_apply,
    principalParts_presheaf_map_apply]
  by_cases hz : (z.1 : X) = y
  · exact hfy z.1 hz _
  · -- `z` is not one of the deleted points, so both principal parts vanish there.
    have hzE : z.1 ∉ E := fun hzE ↦ (Opens.mem_inf.mp z.2).2 (Set.mem_biUnion hzE rfl)
    simp only [E, Set.mem_ofPred_eq, not_and, not_or, not_exists, not_not] at hzE
    obtain ⟨ht, hf'⟩ := hzE hz
    rw [hf', ht (Opens.mem_inf.mp z.2).1]

/-- **`toPrincipalParts D` is an epimorphism** when the codimension-one points are closed. -/
theorem epi_toPrincipalParts (D : SchemeWeilDivisor X) : Epi (toPrincipalParts D) := by
  have hepi : Epi ((Scheme.Modules.toSheaf X).map (toPrincipalParts D)) := by
    refine (TopCat.Sheaf.isLocallySurjective_iff_epi
      ((Scheme.Modules.toSheaf X).map (toPrincipalParts D))).mp ?_
    refine (TopCat.Presheaf.isLocallySurjective_iff _).mpr fun U t y hy ↦ ?_
    obtain ⟨V, i, hyV, s, hs⟩ := exists_toPrincipalParts_app_eq hclosed D t hy
    exact ⟨V, i.le, ⟨s, hs⟩, hyV⟩
  have : (Scheme.Modules.toSheaf X).Faithful :=
    inferInstanceAs (_root_.SheafOfModules.toSheaf X.ringCatSheaf).Faithful
  exact (Scheme.Modules.toSheaf X).epi_of_epi_map hepi

/-- **The short exact sequence of principal parts** `0 ⟶ 𝒪_X(D) ⟶ 𝒦_X ⟶ principalParts D ⟶ 0`, on
a Noetherian integral scheme whose codimension-one points are closed and have discrete valuation
rings as local rings. -/
theorem principalPartsShortComplex_shortExact (D : SchemeWeilDivisor X) :
    (principalPartsShortComplex D).ShortExact :=
  have : Epi (principalPartsShortComplex D).g := epi_toPrincipalParts hclosed D
  have : Mono (principalPartsShortComplex D).f := inferInstanceAs (Mono (sheafι D))
  ⟨principalPartsShortComplex_exact D⟩

end ClosedPoints

end Noetherian

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
