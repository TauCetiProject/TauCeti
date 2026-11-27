/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.Localization.Basic
public import TauCeti.Algebra.Category.CommAlgCat.RestrictScalars

/-!
# Hodge pairs

Let `k` be a commutative ring. A *Hodge pair* over `k` is a commutative `k`-algebra `A` with a
finite ordered index set, here `Fin n`, standing for the pair `(A, Aⁿ)` of `A` and the free
`A`-module `Aⁿ = Fin n → A`. A morphism `(A, Aᵐ) ⟶ (B, Bⁿ)` is a `k`-algebra map `a : A → B`
with an `a`-semilinear map `Aᵐ → Bⁿ`. Hodge pairs are the test objects of Hodge cohomology
(`TauCeti.CategoryTheory.Abelian.FunctorCohomology.Hodge.Basic`): a functor `N` on `k`-algebras
is evaluated on the square-zero extensions `A ⊕ Aⁿ`, and its Ext groups are taken against the
exterior algebras `⋀_A Aⁿ`. This file sets up the category, these two functors, the scalings
`(a, m) ↦ (a, t • m)` and restriction of scalars, and describes the morphisms out of a
localisation `(A[1/g], A[1/g]ⁿ)`.

## Main definitions

* `TauCeti.HodgePair k`: the category of Hodge pairs over `k`.
* `TauCeti.HodgePair.sqZero k`: the functor `(A, Aⁿ) ↦ A ⊕ Aⁿ` (the trivial square-zero
  extension `TrivSqZeroExt A (Fin n → A)`) to commutative `k`-algebras.
* `TauCeti.HodgePair.exterior k`: the functor `(A, Aⁿ) ↦ ⋀_A Aⁿ` to abelian groups (lifted to
  a universe `max u w`), acting on morphisms by the ring maps `TauCeti.HodgePair.exteriorMap f`,
  with the action of `k` on it, `TauCeti.HodgePair.exteriorAction k`.
* `TauCeti.HodgePair.scaleHom P t` and `TauCeti.HodgePair.sqZeroScale k t`: for `t : k`, the
  endomorphism of `(A, Aⁿ)` multiplying `Aⁿ` by `t`, and the induced natural endomorphism
  `s_t : (a, m) ↦ (a, t • m)` of the square-zero extensions.
* `TauCeti.HodgePair.restrictScalars f`: restriction of scalars along a ring map `f : k →+* K`,
  a functor from Hodge pairs over `K` to Hodge pairs over `k`, under which square-zero extensions
  and exterior algebras are unchanged (`TauCeti.HodgePair.sqZeroRestrictScalars`,
  `TauCeti.HodgePair.exteriorRestrictScalars`).
* `TauCeti.HodgePair.ofAlgHom a h`: the morphism `(A, Aⁿ) ⟶ (B, Bⁿ)` applying an algebra map
  `a` coordinatewise.

## Main results

* `TauCeti.HodgePair.homEquivOfIsLocalization`: for a localisation `S` of `A` at a submonoid `M`,
  the morphisms out of `(S, Sⁿ)` are the morphisms out of `(A, Aⁿ)` whose algebra map sends `M`
  to units; `TauCeti.HodgePair.homEquivOfIsLocalizationAway` is the case of `A[1/g]`, whose
  morphisms out are those out of `(A, Aⁿ)` whose algebra map inverts `g`.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean, files
  `src/Lib/General/Geometry/EtaleCharts.lean` (declaration `New.Variety.HodgeTest`) and
  `src/Lib/Cohomology/Hodge/Site.lean` (declarations `New.Variety.HodgeTest.sqZeroExt`,
  `New.Variety.exteriorAlg`, `New.Variety.HodgeTest.existsUnique_lift_away`); Apache 2.0,
  Copyright 2026 Anthropic, PBC. The definitions and the description of morphisms out of
  localisations are adapted from these declarations.
-/

public section

open CategoryTheory

universe w u u' u''

namespace TauCeti

variable (k : Type u') [CommRing k]

/-- A *Hodge pair* over a commutative ring `k`: a commutative `k`-algebra `A` with a natural number
`n`, standing for the pair `(A, Aⁿ)` of `A` and the free `A`-module `Aⁿ = Fin n → A` on the finite
ordered set `Fin n`. -/
structure HodgePair where
  /-- The algebra `A` of the pair `(A, Aⁿ)`. -/
  alg : CommAlgCat.{u} k
  /-- The rank `n` of the free module `Aⁿ` of the pair `(A, Aⁿ)`. -/
  rank : ℕ

namespace HodgePair

variable {k}

/-- A morphism of Hodge pairs `(A, Aᵐ) ⟶ (B, Bⁿ)`: a `k`-algebra map `a : A →ₐ[k] B` with an
`a`-semilinear map `Aᵐ → Bⁿ`. -/
structure Hom (P Q : HodgePair.{u} k) where
  /-- The `k`-algebra map `A → B`. -/
  alg : P.alg →ₐ[k] Q.alg
  /-- The semilinear map `Aᵐ → Bⁿ` over the algebra map. -/
  lin : (Fin P.rank → P.alg) →ₛₗ[(alg : P.alg →+* Q.alg)] (Fin Q.rank → Q.alg)

instance : Category (HodgePair.{u} k) where
  Hom := Hom
  id P := ⟨AlgHom.id k P.alg, LinearMap.id⟩
  comp {P Q R} f g :=
    letI : RingHomCompTriple (f.alg : P.alg →+* Q.alg) (g.alg : Q.alg →+* R.alg)
        ((g.alg.comp f.alg : P.alg →ₐ[k] R.alg) : P.alg →+* R.alg) := ⟨rfl⟩
    ⟨g.alg.comp f.alg, g.lin.comp f.lin⟩

variable {P Q R : HodgePair.{u} k}

/-- Not a `simp` lemma: rewriting the algebra map would change the type of the semilinear map,
on which the `simp` lemmas about `Hom.lin` are stated. Use `id_alg_apply`. -/
lemma id_alg (P : HodgePair.{u} k) : Hom.alg (𝟙 P) = AlgHom.id k P.alg :=
  (rfl)

@[simp]
lemma id_alg_apply (P : HodgePair.{u} k) (a : P.alg) : Hom.alg (𝟙 P) a = a :=
  (rfl)

@[simp]
lemma id_lin (P : HodgePair.{u} k) (v : Fin P.rank → P.alg) : Hom.lin (𝟙 P) v = v :=
  (rfl)

/-- Not a `simp` lemma, for the reason given at `id_alg`. Use `comp_alg_apply`. -/
lemma comp_alg (f : P ⟶ Q) (g : Q ⟶ R) : (f ≫ g).alg = g.alg.comp f.alg :=
  (rfl)

@[simp]
lemma comp_alg_apply (f : P ⟶ Q) (g : Q ⟶ R) (a : P.alg) : (f ≫ g).alg a = g.alg (f.alg a) :=
  (rfl)

@[simp]
lemma comp_lin (f : P ⟶ Q) (g : Q ⟶ R) (v : Fin P.rank → P.alg) :
    (f ≫ g).lin v = g.lin (f.lin v) :=
  (rfl)

/-- Two morphisms of Hodge pairs are equal when their algebra maps and their semilinear maps
agree. -/
@[ext]
lemma hom_ext {f g : P ⟶ Q} (halg : f.alg = g.alg) (hlin : ∀ v, f.lin v = g.lin v) : f = g := by
  obtain ⟨a, l⟩ := f
  obtain ⟨b, l'⟩ := g
  obtain rfl : a = b := halg
  obtain rfl : l = l' := LinearMap.ext hlin
  rfl

/-- The semilinear map of a morphism `(A, Aᵐ) ⟶ (B, Bⁿ)` is determined by the images of the
standard basis vectors: it sends `v` to `∑ i, a (v i) • f(eᵢ)`. -/
lemma lin_apply_eq_sum (f : P ⟶ Q) (v : Fin P.rank → P.alg) :
    f.lin v = ∑ i, f.alg (v i) • f.lin (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← mul_one (v i), ← smul_eq_mul, Pi.single_smul', LinearMap.map_smulₛₗ, smul_eq_mul,
    mul_one, RingHom.coe_coe]

/-- The semilinear map of a morphism of Hodge pairs is semilinear over its algebra map. -/
lemma lin_smul (f : P ⟶ Q) (a : P.alg) (v : Fin P.rank → P.alg) :
    f.lin (a • v) = f.alg a • f.lin v :=
  f.lin.map_smulₛₗ a v

/-- The semilinear map of a morphism of Hodge pairs is `k`-linear. -/
@[simp]
lemma lin_smul_of_tower (f : P ⟶ Q) (t : k) (v : Fin P.rank → P.alg) :
    f.lin (t • v) = t • f.lin v := by
  rw [← algebraMap_smul P.alg t v, lin_smul, AlgHom.commutes, algebraMap_smul]

/-! ### The square-zero extension functor -/

/-- The `k`-algebra map `A ⊕ Aᵐ → B ⊕ Bⁿ`, `(x, m) ↦ (a x, f m)`, of trivial square-zero
extensions induced by a morphism `(a, f) : (A, Aᵐ) ⟶ (B, Bⁿ)` of Hodge pairs. -/
noncomputable def sqZeroMap (f : P ⟶ Q) :
    TrivSqZeroExt P.alg (Fin P.rank → P.alg) →ₐ[k] TrivSqZeroExt Q.alg (Fin Q.rank → Q.alg) :=
  TrivSqZeroExt.lift ((TrivSqZeroExt.inlAlgHom k Q.alg (Fin Q.rank → Q.alg)).comp f.alg)
    { toFun v := TrivSqZeroExt.inr (f.lin v)
      map_add' v w := by rw [map_add, TrivSqZeroExt.inr_add]
      map_smul' t v := by rw [lin_smul_of_tower, TrivSqZeroExt.inr_smul, RingHom.id_apply] }
    (fun _ _ ↦ TrivSqZeroExt.inr_mul_inr _ _ _)
    (fun a v ↦ (congrArg TrivSqZeroExt.inr (lin_smul f a v)).trans
      (TrivSqZeroExt.inl_mul_inr _ _).symm)
    (fun a v ↦ (congrArg (fun w ↦ TrivSqZeroExt.inr (f.lin w)) (op_smul_eq_smul a v)).trans <|
      (congrArg TrivSqZeroExt.inr ((lin_smul f a v).trans (op_smul_eq_smul _ _).symm)).trans
        (TrivSqZeroExt.inr_mul_inl _ _).symm)

@[simp]
lemma fst_sqZeroMap (f : P ⟶ Q) (x : TrivSqZeroExt P.alg (Fin P.rank → P.alg)) :
    (sqZeroMap f x).fst = f.alg x.fst := by
  simp [sqZeroMap, TrivSqZeroExt.lift_def]

@[simp]
lemma snd_sqZeroMap (f : P ⟶ Q) (x : TrivSqZeroExt P.alg (Fin P.rank → P.alg)) :
    (sqZeroMap f x).snd = f.lin x.snd := by
  simp [sqZeroMap, TrivSqZeroExt.lift_def]

variable (k) in
/-- The functor `(A, Aⁿ) ↦ A ⊕ Aⁿ` from Hodge pairs to commutative `k`-algebras, sending a pair to
the trivial square-zero extension `TrivSqZeroExt A (Fin n → A)` and a morphism `(a, f)` to
`(x, m) ↦ (a x, f m)`. -/
-- Exposed: statements about `sqZero` read its values as trivial square-zero extensions.
@[expose] noncomputable def sqZero : HodgePair.{u} k ⥤ CommAlgCat.{u} k where
  obj P := CommAlgCat.of k (TrivSqZeroExt P.alg (Fin P.rank → P.alg))
  map f := CommAlgCat.ofHom (sqZeroMap f)
  map_id P := by
    ext1
    exact AlgHom.ext fun x ↦ TrivSqZeroExt.ext (by simp) (by simp)
  map_comp f g := by
    ext1
    exact AlgHom.ext fun x ↦ TrivSqZeroExt.ext (by simp) (by simp)

lemma sqZero_obj (P : HodgePair.{u} k) :
    (sqZero k).obj P = CommAlgCat.of k (TrivSqZeroExt P.alg (Fin P.rank → P.alg)) :=
  (rfl)

lemma sqZero_map (f : P ⟶ Q) : (sqZero k).map f = CommAlgCat.ofHom (sqZeroMap f) :=
  (rfl)

@[simp]
lemma fst_sqZero_map (f : P ⟶ Q) (x : (sqZero k).obj P) :
    ((sqZero k).map f x).fst = f.alg x.fst :=
  fst_sqZeroMap f x

@[simp]
lemma snd_sqZero_map (f : P ⟶ Q) (x : (sqZero k).obj P) :
    ((sqZero k).map f x).snd = f.lin x.snd :=
  snd_sqZeroMap f x

/-! ### The exterior algebra functor -/

/-- The ring map `⋀_A Aᵐ → ⋀_B Bⁿ` induced by a morphism `(a, f) : (A, Aᵐ) ⟶ (B, Bⁿ)` of Hodge
pairs: it is `a` on scalars and sends `ι v` to `ι (f v)`. -/
noncomputable def exteriorMap (f : P ⟶ Q) :
    ExteriorAlgebra P.alg (Fin P.rank → P.alg) →+* ExteriorAlgebra Q.alg (Fin Q.rank → Q.alg) :=
  letI := Algebra.compHom (ExteriorAlgebra Q.alg (Fin Q.rank → Q.alg)) (f.alg : P.alg →+* Q.alg)
  (ExteriorAlgebra.lift P.alg
    ⟨{ toFun v := ExteriorAlgebra.ι Q.alg (f.lin v)
       map_add' v w := by rw [map_add, map_add]
       map_smul' a v := by rw [lin_smul, LinearMap.map_smul, RingHom.id_apply,
         Algebra.compHom_smul_def, RingHom.coe_coe] },
      fun v ↦ ExteriorAlgebra.ι_sq_zero _⟩).toRingHom

@[simp]
lemma exteriorMap_ι (f : P ⟶ Q) (v : Fin P.rank → P.alg) :
    exteriorMap f (ExteriorAlgebra.ι P.alg v) = ExteriorAlgebra.ι Q.alg (f.lin v) :=
  letI := Algebra.compHom (ExteriorAlgebra Q.alg (Fin Q.rank → Q.alg)) (f.alg : P.alg →+* Q.alg)
  ExteriorAlgebra.lift_ι_apply P.alg _ _ v

@[simp]
lemma exteriorMap_algebraMap (f : P ⟶ Q) (a : P.alg) :
    exteriorMap f (algebraMap P.alg _ a) = algebraMap Q.alg _ (f.alg a) :=
  letI := Algebra.compHom (ExteriorAlgebra Q.alg (Fin Q.rank → Q.alg)) (f.alg : P.alg →+* Q.alg)
  AlgHom.commutes (ExteriorAlgebra.lift P.alg _) a

/-- `exteriorMap f` is `k`-linear, since the algebra map of `f` is a `k`-algebra map. -/
@[simp]
lemma exteriorMap_smul (f : P ⟶ Q) (t : k) (x : ExteriorAlgebra P.alg (Fin P.rank → P.alg)) :
    exteriorMap f (t • x) = t • exteriorMap f x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply k P.alg,
    exteriorMap_algebraMap, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

/-- `exteriorMap f` is determined by its values on scalars and on the generators `ι v`. -/
private lemma exteriorMap_ext {S : Type*} [Semiring S]
    {φ ψ : ExteriorAlgebra P.alg (Fin P.rank → P.alg) →+* S}
    (halg : ∀ a, φ (algebraMap P.alg _ a) = ψ (algebraMap P.alg _ a))
    (hι : ∀ v, φ (ExteriorAlgebra.ι P.alg v) = ψ (ExteriorAlgebra.ι P.alg v)) : φ = ψ :=
  RingHom.ext fun x ↦ by
    induction x using ExteriorAlgebra.induction with
    | algebraMap a => exact halg a
    | ι v => exact hι v
    | mul x y hx hy => rw [map_mul, map_mul, hx, hy]
    | add x y hx hy => rw [map_add, map_add, hx, hy]

@[simp]
lemma exteriorMap_id (P : HodgePair.{u} k) : exteriorMap (𝟙 P) = RingHom.id _ :=
  exteriorMap_ext (by simp) (by simp)

lemma exteriorMap_comp (f : P ⟶ Q) (g : Q ⟶ R) :
    exteriorMap (f ≫ g) = (exteriorMap g).comp (exteriorMap f) :=
  exteriorMap_ext (by simp) (by simp)

variable (k) in
/-- The functor `(A, Aⁿ) ↦ ⋀_A Aⁿ` from Hodge pairs to abelian groups, sending a morphism to
`exteriorMap`. Its values are lifted to the universe `max u w`, so that it serves as a coefficient
for functors with values in any universe containing that of the algebras. -/
-- Exposed: statements about `exterior` read its values as lifted exterior algebras.
@[expose] noncomputable def exterior : HodgePair.{u} k ⥤ AddCommGrpCat.{max u w} where
  obj P := AddCommGrpCat.of (ULift.{w} (ExteriorAlgebra P.alg (Fin P.rank → P.alg)))
  map f := AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
    ((exteriorMap f).toAddMonoidHom.comp AddEquiv.ulift.toAddMonoidHom))
  map_id P := by
    ext x
    simp
  map_comp f g := by
    ext x
    simp [exteriorMap_comp]

lemma exterior_obj (P : HodgePair.{u} k) :
    (exterior.{w} k).obj P =
      AddCommGrpCat.of (ULift.{w} (ExteriorAlgebra P.alg (Fin P.rank → P.alg))) :=
  (rfl)

@[simp]
lemma exterior_map_down (f : P ⟶ Q) (x : (exterior.{w} k).obj P) :
    ((exterior.{w} k).map f x).down = exteriorMap f x.down :=
  (rfl)

variable (k) in
/-- The action of `k` on the exterior algebra functor: `t : k` acts on each `⋀_A Aⁿ` by scalar
multiplication, which commutes with the maps `exteriorMap f` since these are `k`-linear. This makes
Ext groups with values in `exterior k` into `k`-modules. -/
noncomputable def exteriorAction : k →+* End (exterior.{w, u} k) where
  -- Each identity below is checked on the underlying element `x.down` of the exterior algebra.
  toFun t := .of
    { app P := AddCommGrpCat.ofHom
        (DistribSMul.toAddMonoidHom (ULift.{w} (ExteriorAlgebra P.alg (Fin P.rank → P.alg))) t)
      naturality P Q f := by
        ext x
        exact ULift.ext (exteriorMap_smul f t x.down).symm }
  map_one' := by
    ext P x
    exact ULift.ext (one_smul k x.down)
  map_mul' s t := by
    ext P x
    exact ULift.ext (mul_smul s t x.down)
  map_zero' := by
    ext P x
    exact ULift.ext (zero_smul k x.down)
  map_add' s t := by
    ext P x
    exact ULift.ext (add_smul s t x.down)

@[simp]
lemma exteriorAction_app_down (t : k) (P : HodgePair.{u} k) (x : (exterior.{w} k).obj P) :
    ((exteriorAction.{w} k t).asHom.app P x).down = t • x.down :=
  (rfl)

/-! ### Scaling -/

/-- For `t : k`, the endomorphism of a Hodge pair `(A, Aⁿ)` that is the identity of `A` and
multiplication by `t` on `Aⁿ`. -/
def scaleHom (P : HodgePair.{u} k) (t : k) : P ⟶ P :=
  ⟨AlgHom.id k P.alg,
    { toFun v := t • v
      map_add' := smul_add t
      map_smul' a v := smul_comm t a v }⟩

@[simp]
lemma scaleHom_alg_apply (P : HodgePair.{u} k) (t : k) (a : P.alg) : (scaleHom P t).alg a = a :=
  (rfl)

@[simp]
lemma scaleHom_lin (P : HodgePair.{u} k) (t : k) (v : Fin P.rank → P.alg) :
    (scaleHom P t).lin v = t • v :=
  (rfl)

/-- Morphisms of Hodge pairs commute with the scalings. -/
@[reassoc]
lemma comp_scaleHom (f : P ⟶ Q) (t : k) : f ≫ scaleHom Q t = scaleHom P t ≫ f :=
  hom_ext rfl fun v ↦ (lin_smul_of_tower f t v).symm

@[simp]
lemma scaleHom_one (P : HodgePair.{u} k) : scaleHom P 1 = 𝟙 P :=
  hom_ext rfl fun v ↦ one_smul k v

lemma scaleHom_mul (P : HodgePair.{u} k) (s t : k) :
    scaleHom P (s * t) = scaleHom P t ≫ scaleHom P s :=
  hom_ext rfl fun v ↦ mul_smul s t v

variable (k) in
/-- The *scaling* `s_t : (a, m) ↦ (a, t • m)` of the square-zero extensions `A ⊕ Aⁿ`, a natural
endomorphism of `sqZero k` whose components are the images of the endomorphisms `scaleHom P t`. -/
noncomputable def sqZeroScale (t : k) : sqZero.{u} k ⟶ sqZero k where
  app P := (sqZero k).map (scaleHom P t)
  naturality P Q f := by rw [← Functor.map_comp, ← Functor.map_comp, comp_scaleHom]

lemma sqZeroScale_app (t : k) (P : HodgePair.{u} k) :
    (sqZeroScale k t).app P = (sqZero k).map (scaleHom P t) :=
  (rfl)

@[simp]
lemma fst_sqZeroScale_app (t : k) (P : HodgePair.{u} k) (x : (sqZero k).obj P) :
    ((sqZeroScale k t).app P x).fst = x.fst := by
  simp [sqZeroScale_app]

@[simp]
lemma snd_sqZeroScale_app (t : k) (P : HodgePair.{u} k) (x : (sqZero k).obj P) :
    ((sqZeroScale k t).app P x).snd = t • x.snd := by
  simp [sqZeroScale_app]

@[simp]
lemma sqZeroScale_one : sqZeroScale.{u} k 1 = 𝟙 _ := by
  ext P : 2
  simp [sqZeroScale_app]

lemma sqZeroScale_mul (s t : k) :
    sqZeroScale.{u} k (s * t) = sqZeroScale k t ≫ sqZeroScale k s := by
  ext P : 2
  simp [sqZeroScale_app, scaleHom_mul]

/-! ### Restriction of scalars -/

variable {K : Type u''} [CommRing K]

/-- Restriction of scalars along a ring map `f : k →+* K`: a Hodge pair `(A, Aⁿ)` over `K` is a
Hodge pair over `k`, with the same free module and the same morphisms. -/
-- Exposed: the comparisons with `sqZero` and `exterior` below identify objects definitionally.
@[expose] noncomputable def restrictScalars (f : k →+* K) :
    HodgePair.{u} K ⥤ HodgePair.{u} k where
  obj P := ⟨CommAlgCat.restrictScalarsObj f P.alg, P.rank⟩
  map g := ⟨(CommAlgCat.restrictScalarsMap f (CommAlgCat.ofHom g.alg)).hom, g.lin⟩

lemma restrictScalars_obj_rank (f : k →+* K) (P : HodgePair.{u} K) :
    ((restrictScalars f).obj P).rank = P.rank :=
  (rfl)

/-- Not a `simp` lemma: the two sides are typed with different algebra structures on the same
ring. -/
lemma restrictScalars_map_alg_apply (f : k →+* K) {P Q : HodgePair.{u} K} (g : P ⟶ Q)
    (a : P.alg) : ((restrictScalars f).map g).alg a = g.alg a :=
  (rfl)

/-- Not a `simp` lemma, for the reason given at `restrictScalars_map_alg_apply`. -/
lemma restrictScalars_map_lin (f : k →+* K) {P Q : HodgePair.{u} K} (g : P ⟶ Q)
    (v : Fin P.rank → P.alg) : ((restrictScalars f).map g).lin v = g.lin v :=
  (rfl)

/-- Square-zero extensions commute with restriction of scalars along `f : k →+* K`: the identity
maps of the algebras `A ⊕ Aⁿ`. -/
noncomputable def sqZeroRestrictScalars (f : k →+* K) :
    sqZero K ⋙ CommAlgCat.restrictScalars f ⟶ restrictScalars f ⋙ sqZero k where
  app P := 𝟙 ((restrictScalars f ⋙ sqZero k).obj P)
  naturality P Q g := by
    -- Both composites are `sqZeroMap g` on the same underlying ring `A ⊕ Aⁿ`; only the
    -- `k`-algebra structures differ in how they are written.
    ext x
    rfl

@[simp]
lemma sqZeroRestrictScalars_app (f : k →+* K) (P : HodgePair.{u} K) :
    (sqZeroRestrictScalars f).app P = 𝟙 _ :=
  (rfl)

/-- The identification `sqZeroRestrictScalars f` turns the scaling by `f t` into the scaling by
`t`. -/
lemma whiskerRight_sqZeroScale_comp_sqZeroRestrictScalars (f : k →+* K) (t : k) :
    Functor.whiskerRight (sqZeroScale K (f t)) (CommAlgCat.restrictScalars f) ≫
        sqZeroRestrictScalars f =
      sqZeroRestrictScalars f ≫ Functor.whiskerLeft (restrictScalars f) (sqZeroScale k t) := by
  -- Both sides are `(a, m) ↦ (a, f t • m)`: `t` acts on the restricted algebra through `f`.
  ext P x
  rfl

/-- Exterior algebras commute with restriction of scalars along `f : k →+* K`: the identity maps of
the groups `⋀_A Aⁿ`. -/
noncomputable def exteriorRestrictScalars (f : k →+* K) :
    restrictScalars f ⋙ exterior.{w} k ⟶ exterior.{w, u} K where
  app P := 𝟙 _
  naturality P Q g := by
    -- Both composites are `exteriorMap g` on the same exterior algebra `⋀_A Aⁿ`.
    ext x
    rfl

@[simp]
lemma exteriorRestrictScalars_app (f : k →+* K) (P : HodgePair.{u} K) :
    (exteriorRestrictScalars.{w} f).app P = 𝟙 _ :=
  (rfl)

/-- The identification `exteriorRestrictScalars f` turns the action of `t : k` into the action of
`f t`. -/
lemma whiskerLeft_exteriorAction_comp_exteriorRestrictScalars (f : k →+* K) (t : k) :
    Functor.whiskerLeft (restrictScalars f) (exteriorAction.{w, u} k t).asHom ≫
        exteriorRestrictScalars f =
      exteriorRestrictScalars f ≫ (exteriorAction.{w, u} K (f t)).asHom := by
  -- `t` acts on the exterior algebra of the restricted algebra through `f`, by definition.
  ext P x
  rfl

/-! ### Morphisms out of localisations -/

/-- The morphism `(A, Aⁿ) ⟶ (B, Bⁿ)` of Hodge pairs with the same rank induced by a `k`-algebra
map `a : A → B`, applying `a` to each coordinate of `Aⁿ`. -/
def ofAlgHom {P Q : HodgePair.{u} k} (a : P.alg →ₐ[k] Q.alg) (h : P.rank = Q.rank) : P ⟶ Q :=
  ⟨a,
    { toFun v i := a (v (Fin.cast h.symm i))
      map_add' _ _ := funext fun _ ↦ map_add a _ _
      map_smul' c _ := funext fun _ ↦ map_mul a c _ }⟩

@[simp]
lemma ofAlgHom_alg_apply (a : P.alg →ₐ[k] Q.alg) (h : P.rank = Q.rank) (x : P.alg) :
    (ofAlgHom a h).alg x = a x :=
  (rfl)

@[simp]
lemma ofAlgHom_lin (a : P.alg →ₐ[k] Q.alg) (h : P.rank = Q.rank) (v : Fin P.rank → P.alg)
    (i : Fin Q.rank) : (ofAlgHom a h).lin v i = a (v (Fin.cast h.symm i)) :=
  (rfl)

@[simp]
lemma ofAlgHom_lin_single (a : P.alg →ₐ[k] Q.alg) (h : P.rank = Q.rank) (i : Fin P.rank)
    (x : P.alg) : (ofAlgHom a h).lin (Pi.single i x) = Pi.single (Fin.cast h i) (a x) := by
  ext j
  by_cases hj : j = Fin.cast h i
  · simp [hj]
  · rw [ofAlgHom_lin, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne fun hi ↦ hj (by simp [← hi]),
      map_zero]

section Localization

variable {P L : HodgePair.{u} k} (M : Submonoid P.alg) [Algebra P.alg L.alg]
  [IsScalarTower k P.alg L.alg] [IsLocalization M L.alg] (h : P.rank = L.rank)

/-- The morphism out of `(S, Sⁿ)`, for `S` the localisation of `A` at `M`, extending a morphism `f`
out of `(A, Aⁿ)` whose algebra map sends `M` to units: its algebra map is the lift of `f.alg` to the
localisation, and it sends `v` to `∑ i, a (v i) • f(eᵢ)`. -/
private noncomputable def liftOfIsLocalization {Q : HodgePair.{u} k} (f : P ⟶ Q)
    (hf : ∀ m ∈ M, IsUnit (f.alg m)) : L ⟶ Q :=
  let a : L.alg →ₐ[k] Q.alg :=
    IsLocalization.liftAlgHom (M := M) (f := f.alg) fun m ↦ hf m m.property
  ⟨a,
    { toFun v := ∑ i, a (v i) • f.lin (Pi.single (Fin.cast h.symm i) 1)
      map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
      map_smul' c v := by simp [mul_smul, Finset.smul_sum] }⟩

private lemma liftOfIsLocalization_alg {Q : HodgePair.{u} k} (f : P ⟶ Q)
    (hf : ∀ m ∈ M, IsUnit (f.alg m)) :
    (liftOfIsLocalization M h f hf).alg =
      IsLocalization.liftAlgHom (M := M) (f := f.alg) (fun m ↦ hf m m.property) :=
  (rfl)

private lemma liftOfIsLocalization_lin {Q : HodgePair.{u} k} (f : P ⟶ Q)
    (hf : ∀ m ∈ M, IsUnit (f.alg m)) (v : Fin L.rank → L.alg) :
    (liftOfIsLocalization M h f hf).lin v =
      ∑ i, IsLocalization.liftAlgHom (M := M) (f := f.alg) (fun m ↦ hf m m.property) (v i) •
        f.lin (Pi.single (Fin.cast h.symm i) 1) :=
  (rfl)

private lemma ofAlgHom_comp_liftOfIsLocalization {Q : HodgePair.{u} k} (f : P ⟶ Q)
    (hf : ∀ m ∈ M, IsUnit (f.alg m)) :
    ofAlgHom (IsScalarTower.toAlgHom k P.alg L.alg) h ≫ liftOfIsLocalization M h f hf = f := by
  refine hom_ext (AlgHom.ext fun a ↦ ?_) fun v ↦ ?_
  · rw [comp_alg_apply, liftOfIsLocalization_alg, ofAlgHom_alg_apply]
    exact IsLocalization.lift_eq _ a
  · rw [comp_lin, liftOfIsLocalization_lin, lin_apply_eq_sum f v]
    refine Fintype.sum_equiv (finCongr h.symm) _ _ fun i ↦ ?_
    simp [IsLocalization.lift_eq]

/-- **Morphisms out of a localisation.** Let `L = (S, Sⁿ)` be a Hodge pair whose algebra `S` is the
localisation of the algebra `A` of `P = (A, Aⁿ)` at a submonoid `M`, with the same index set as
`P`. Precomposition with `(A, Aⁿ) ⟶ (S, Sⁿ)` identifies the morphisms out of `L` with the morphisms
out of `P` whose algebra map sends every element of `M` to a unit. -/
noncomputable def homEquivOfIsLocalization (Q : HodgePair.{u} k) :
    (L ⟶ Q) ≃ {f : P ⟶ Q // ∀ m ∈ M, IsUnit (f.alg m)} where
  toFun g := ⟨ofAlgHom (IsScalarTower.toAlgHom k P.alg L.alg) h ≫ g, fun m hm ↦ by
    rw [comp_alg_apply, ofAlgHom_alg_apply]
    exact (IsLocalization.map_units L.alg ⟨m, hm⟩).map g.alg⟩
  invFun f := liftOfIsLocalization M h f.val f.property
  left_inv g := by
    have hg : ∀ m ∈ M, IsUnit ((ofAlgHom (IsScalarTower.toAlgHom k P.alg L.alg) h ≫ g).alg m) :=
      fun m hm ↦ by
        rw [comp_alg_apply, ofAlgHom_alg_apply]
        exact (IsLocalization.map_units L.alg ⟨m, hm⟩).map g.alg
    have halg : (liftOfIsLocalization M h _ hg).alg = g.alg :=
      AlgHom.toRingHom_injective <| IsLocalization.ringHom_ext M <| RingHom.ext fun a ↦ by
        rw [liftOfIsLocalization_alg]
        simp [IsLocalization.lift_eq]
    refine hom_ext halg fun v ↦ ?_
    rw [liftOfIsLocalization_lin, lin_apply_eq_sum g v, ← liftOfIsLocalization_alg M h _ hg, halg]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [comp_lin, ofAlgHom_lin_single, map_one, Fin.cast_cast, Fin.cast_eq_self]
  right_inv f := Subtype.ext (ofAlgHom_comp_liftOfIsLocalization M h f.val f.property)

@[simp]
lemma homEquivOfIsLocalization_apply_coe (Q : HodgePair.{u} k) (g : L ⟶ Q) :
    (homEquivOfIsLocalization M h Q g : P ⟶ Q) =
      ofAlgHom (IsScalarTower.toAlgHom k P.alg L.alg) h ≫ g :=
  (rfl)

/-- The morphism out of the localisation given by `homEquivOfIsLocalization` extends `f`. -/
@[simp]
lemma ofAlgHom_comp_homEquivOfIsLocalization_symm_apply (Q : HodgePair.{u} k)
    (f : {f : P ⟶ Q // ∀ m ∈ M, IsUnit (f.alg m)}) :
    ofAlgHom (IsScalarTower.toAlgHom k P.alg L.alg) h ≫ (homEquivOfIsLocalization M h Q).symm f =
      f :=
  congrArg Subtype.val ((homEquivOfIsLocalization M h Q).apply_symm_apply f)

end Localization

section Away

variable {P L : HodgePair.{u} k} (g : P.alg) [Algebra P.alg L.alg] [IsScalarTower k P.alg L.alg]
  [IsLocalization.Away g L.alg] (h : P.rank = L.rank)

/-- **Morphisms out of `(A[1/g], A[1/g]ⁿ)`.** For a Hodge pair `L` whose algebra is the
localisation `A[1/g]` of the algebra `A` of `P = (A, Aⁿ)`, with the same index set as `P`,
precomposition with `(A, Aⁿ) ⟶ (A[1/g], A[1/g]ⁿ)` identifies the morphisms out of `L` with the
morphisms out of `P` whose algebra map sends `g` to a unit. -/
noncomputable def homEquivOfIsLocalizationAway (Q : HodgePair.{u} k) :
    (L ⟶ Q) ≃ {f : P ⟶ Q // IsUnit (f.alg g)} :=
  (homEquivOfIsLocalization (Submonoid.powers g) h Q).trans <| Equiv.subtypeEquivRight fun f ↦
    ⟨fun hf ↦ hf g (Submonoid.mem_powers g), by
      rintro hf _ ⟨n, rfl⟩
      rw [map_pow]
      exact hf.pow n⟩

@[simp]
lemma homEquivOfIsLocalizationAway_apply_coe (Q : HodgePair.{u} k) (f : L ⟶ Q) :
    (homEquivOfIsLocalizationAway g h Q f : P ⟶ Q) =
      ofAlgHom (IsScalarTower.toAlgHom k P.alg L.alg) h ≫ f :=
  (rfl)

/-- The morphism out of `(A[1/g], A[1/g]ⁿ)` given by `homEquivOfIsLocalizationAway` extends `f`. -/
@[simp]
lemma ofAlgHom_comp_homEquivOfIsLocalizationAway_symm_apply (Q : HodgePair.{u} k)
    (f : {f : P ⟶ Q // IsUnit (f.alg g)}) :
    ofAlgHom (IsScalarTower.toAlgHom k P.alg L.alg) h ≫
        (homEquivOfIsLocalizationAway g h Q).symm f = f :=
  congrArg Subtype.val ((homEquivOfIsLocalizationAway g h Q).apply_symm_apply f)

end Away

end HodgePair

end TauCeti
