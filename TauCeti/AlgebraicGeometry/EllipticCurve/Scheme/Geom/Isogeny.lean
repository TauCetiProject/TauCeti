/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Hom
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Rank
public import TauCeti.AlgebraicGeometry.GroupScheme.FiniteFlat
public import TauCeti.AlgebraicGeometry.GroupScheme.Rank
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank

/-!
# Isogenies of elliptic curves over a scheme and their degree

Let `E` and `E'` be elliptic curves over a scheme `S`. A homomorphism `f : E ⟶ E'` of elliptic
curves over `S` (a morphism `E.toCommGrp ⟶ E'.toCommGrp` of commutative group schemes) is an
**isogeny** when its underlying morphism of schemes is finite, flat and surjective
(`EllipticCurveGeom.IsIsogeny`). Every homomorphism of elliptic curves is locally of finite
presentation (`EllipticCurveGeom.locallyOfFinitePresentation_hom_hom_hom_left`), so an isogeny is
finite locally free.

The rank of a finite locally free morphism is a locally constant function on its target. For an
isogeny it is constant along the fibres of `E' ⟶ S`, since translations of `E'` by points in the
image of `f` preserve it (`TauCeti.GroupScheme.finrank_left_eq`). It is therefore a function on
the base, the **degree** of `f` (`EllipticCurveGeom.degree`): at `s ∈ S`, the rank of `f` at the
zero of the fibre over `s`. The degree is locally constant and positive, but over a disconnected
base it need not be constant. An isogeny of constant degree `n` is an **isogeny of degree `n`**
(`EllipticCurveGeom.IsogenyOfDegree`).

The kernel `ker f` of an isogeny is a finite locally free commutative group scheme over `S`
(`EllipticCurveGeom.IsIsogeny.kernel`), whose rank at `s` is the degree of `f` at `s`.

Isomorphisms are the isogenies of degree one, and isogenies compose, with degrees multiplying
pointwise on the base. Over a field, multiplication by a nonzero integer `n` is an isogeny of degree
`n²`.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsIsogeny f`: the homomorphism `f` is an isogeny.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.degree f`: the degree of `f`, a function `S → ℕ`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsogenyOfDegree f n`: `f` is an isogeny of constant
  degree `n`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsIsogeny.kernel f`: the kernel of an isogeny, as a
  finite locally free commutative group scheme over `S`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.finrank_hom_hom_hom_left`: the rank of an isogeny at
  a point of `E'` over `s` is the degree at `s`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isLocallyConstant_degree` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.degree_pos`: the degree of an isogeny is locally
  constant and positive.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isogenyOfDegree_iff_forall_finrank_hom_hom_hom_left`:
  an isogeny has degree `n` exactly when its underlying morphism of schemes has constant rank `n`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsIsogeny.finrank_kernel`: the rank of `ker f` is the
  degree; so `f` has degree `n` exactly when `ker f` has constant rank `n`
  (`TauCeti.AlgebraicGeometry.EllipticCurveGeom.isogenyOfDegree_iff_forall_finrank_kernel`).
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isIso_iff_isogenyOfDegree_one`: an isogeny is an
  isomorphism exactly when it has degree one; in particular an isomorphism has degree one
  (`TauCeti.AlgebraicGeometry.EllipticCurveGeom.degree_eq_one_of_isIso`).
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.degree_comp`: degrees multiply under composition, at
  every point of the base; so `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsogenyOfDegree.comp`:
  composing isogenies of degrees `m` and `n` gives an isogeny of degree `m * n`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isogenyOfDegree_intCast`: over a field,
  multiplication by a nonzero integer `n` is an isogeny of degree `n²`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §2.4 and 2.3.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} {E E' E'' : EllipticCurveGeom S}

/-! ### Isogenies -/

/-- **Isogenies of elliptic curves.** A homomorphism `f : E ⟶ E'` of elliptic curves over `S` is an
isogeny when its underlying morphism of schemes is finite, flat and surjective (Katz–Mazur §2.4).
It is then finite locally free, since it is locally of finite presentation like every homomorphism
of elliptic curves (`locallyOfFinitePresentation_hom_hom_hom_left`). -/
class IsIsogeny (f : E.toCommGrp ⟶ E'.toCommGrp) : Prop where
  /-- The underlying morphism of schemes is finite. -/
  isFinite : IsFinite f.hom.hom.hom.left
  /-- The underlying morphism of schemes is flat. -/
  flat : Flat f.hom.hom.hom.left
  /-- The underlying morphism of schemes is surjective. -/
  surjective : Surjective f.hom.hom.hom.left

attribute [instance] IsIsogeny.isFinite IsIsogeny.flat IsIsogeny.surjective

/-- An isomorphism of elliptic curves is an isogeny. -/
instance isIsogeny_of_isIso (f : E.toCommGrp ⟶ E'.toCommGrp) [IsIso f] : IsIsogeny f := by
  have : IsIso f.hom.hom.hom.left := isIso_iff_isIso_hom_hom_hom_left.mp ‹_›
  constructor <;> infer_instance

/-- The composite of two isogenies is an isogeny. -/
instance isIsogeny_comp (f : E.toCommGrp ⟶ E'.toCommGrp) (g : E'.toCommGrp ⟶ E''.toCommGrp)
    [IsIsogeny f] [IsIsogeny g] : IsIsogeny (f ≫ g) := by
  have h : (f ≫ g).hom.hom.hom.left = f.hom.hom.hom.left ≫ g.hom.hom.hom.left := by simp
  constructor <;> rw [h] <;> infer_instance

/-! ### The degree -/

/-- **The degree of a homomorphism of elliptic curves**, as a function on the base: at `s ∈ S`, the
rank of the underlying morphism of schemes at the zero of the fibre of `E'` over `s`. For an
isogeny this is its rank at every point of that fibre (`finrank_hom_hom_hom_left`) and the rank of
its kernel at `s` (`IsIsogeny.finrank_kernel`). -/
noncomputable def degree (f : E.toCommGrp ⟶ E'.toCommGrp) (s : S) : ℕ :=
  f.hom.hom.hom.left.finrank (E'.zero s)

/-- The degree of `f` at `s` is the rank of `f` at the zero of the fibre of `E'` over `s`. -/
theorem degree_apply (f : E.toCommGrp ⟶ E'.toCommGrp) (s : S) :
    degree f s = f.hom.hom.hom.left.finrank (E'.zero s) :=
  (rfl)

/-- **Isogenies of degree `n`.** The homomorphism `f` is an isogeny whose degree is `n` at every
point of the base. Over a disconnected base an isogeny need not have a degree in this sense. -/
structure IsogenyOfDegree (f : E.toCommGrp ⟶ E'.toCommGrp) (n : ℕ) : Prop where
  /-- `f` is an isogeny. -/
  isIsogeny : IsIsogeny f
  /-- The degree of `f` is `n` at every point of the base. -/
  degree_eq : ∀ s, degree f s = n

variable (f : E.toCommGrp ⟶ E'.toCommGrp) [IsIsogeny f]

/-- An isogeny has degree `n` exactly when its degree is `n` at every point of the base. -/
theorem isogenyOfDegree_iff {n : ℕ} : IsogenyOfDegree f n ↔ ∀ s, degree f s = n :=
  ⟨IsogenyOfDegree.degree_eq, fun h ↦ ⟨‹_›, h⟩⟩

/-- **The rank of an isogeny is its degree.** The rank of an isogeny `f : E ⟶ E'` at a point `y`
of `E'` is the degree of `f` at the image of `y` in `S`. -/
theorem finrank_hom_hom_hom_left (y : E'.carrier) :
    f.hom.hom.hom.left.finrank y = degree f (E'.structureMap y) := by
  rw [GroupScheme.finrank_left_eq f.hom.hom.hom y, degree_apply]
  simp

/-- The degree of an isogeny is locally constant on the base. -/
theorem isLocallyConstant_degree : IsLocallyConstant (degree f) :=
  f.hom.hom.hom.left.isLocallyConstant_finrank.comp_continuous E'.zero.continuous

/-- The degree of an isogeny is positive. -/
theorem degree_pos (s : S) : 0 < degree f s :=
  (f.hom.hom.hom.left.one_le_finrank_iff_surjective.mpr inferInstance) (E'.zero s)

/-- An isogeny has degree `n` exactly when its underlying morphism of schemes has constant rank
`n`. -/
theorem isogenyOfDegree_iff_forall_finrank_hom_hom_hom_left {n : ℕ} :
    IsogenyOfDegree f n ↔ ∀ y, f.hom.hom.hom.left.finrank y = n := by
  rw [isogenyOfDegree_iff]
  exact ⟨fun h y ↦ by rw [finrank_hom_hom_hom_left, h], fun h s ↦ h _⟩

/-! ### The kernel -/

/-- **The kernel of an isogeny**, the scheme-theoretic kernel of `f`, as a finite locally free
commutative group scheme over `S`. Its rank is the degree of `f` (`IsIsogeny.finrank_kernel`). -/
noncomputable def IsIsogeny.kernel : FiniteFlatCommGroupScheme S where
  carrier := (Limits.kernel (Grp.ofHom f.hom.hom.hom)).X.left
  structureMap := (Limits.kernel (Grp.ofHom f.hom.hom.hom)).X.hom
  grp := inferInstanceAs (GrpObj (Limits.kernel (Grp.ofHom f.hom.hom.hom)).X)
  comm := inferInstanceAs (IsCommMonObj (Limits.kernel (Grp.ofHom f.hom.hom.hom)).X)
  finite :=
    have : IsFinite (Grp.ofHom f.hom.hom.hom).hom.hom.left := ‹IsIsogeny f›.isFinite
    inferInstance
  flat :=
    have : Flat (Grp.ofHom f.hom.hom.hom).hom.hom.left := ‹IsIsogeny f›.flat
    inferInstance
  locallyOfFinitePresentation :=
    have : LocallyOfFinitePresentation (Grp.ofHom f.hom.hom.hom).hom.hom.left :=
      locallyOfFinitePresentation_hom_hom_hom_left f
    inferInstance

/-- **The rank of the kernel of an isogeny is its degree.** -/
theorem IsIsogeny.finrank_kernel (s : S) :
    (IsIsogeny.kernel f).structureMap.finrank s = degree f s := by
  have : IsFinite (Grp.ofHom f.hom.hom.hom).hom.hom.left := ‹IsIsogeny f›.isFinite
  have : Flat (Grp.ofHom f.hom.hom.hom).hom.hom.left := ‹IsIsogeny f›.flat
  rw [degree_apply, ← one_left]
  exact GroupScheme.finrank_kernel_hom (Grp.ofHom f.hom.hom.hom) s

/-- An isogeny has degree `n` exactly when its kernel has constant rank `n`. -/
theorem isogenyOfDegree_iff_forall_finrank_kernel {n : ℕ} :
    IsogenyOfDegree f n ↔ ∀ s, (IsIsogeny.kernel f).structureMap.finrank s = n := by
  simp only [isogenyOfDegree_iff, IsIsogeny.finrank_kernel]

/-- **An isogeny is an isomorphism exactly when it has degree one.** -/
theorem isIso_iff_isogenyOfDegree_one : IsIso f ↔ IsogenyOfDegree f 1 := by
  rw [isIso_iff_isIso_hom_hom_hom_left, Scheme.Hom.isIso_iff_finrank_eq, funext_iff,
    isogenyOfDegree_iff_forall_finrank_hom_hom_hom_left]
  simp only [Pi.one_apply]

/-- An isomorphism of elliptic curves has degree one. -/
@[simp]
theorem degree_eq_one_of_isIso (f : E.toCommGrp ⟶ E'.toCommGrp) [IsIso f] (s : S) :
    degree f s = 1 :=
  ((isIso_iff_isogenyOfDegree_one f).mp ‹_›).degree_eq s

/-- **Degrees multiply under composition.** At every point `s` of `S`, the degree of the composite
of isogenies `f : E ⟶ E'` and `g : E' ⟶ E''` is the product of their degrees at `s`. -/
theorem degree_comp (g : E'.toCommGrp ⟶ E''.toCommGrp) [IsIsogeny g] (s : S) :
    degree (f ≫ g) s = degree f s * degree g s := by
  have h : (f ≫ g).hom.hom.hom.left = f.hom.hom.hom.left ≫ g.hom.hom.hom.left := by simp
  rw [degree_apply, degree_apply, degree_apply, h]
  -- the fibre of `g` over the zero of `E''` above `s` lies over `s`, where `f` has rank
  -- `degree f s`
  refine Scheme.Hom.finrank_comp_of_fiber _ _ fun y hy ↦ ?_
  have hys : E'.structureMap y = s := by
    rw [← show g.hom.hom.hom.left ≫ E''.structureMap = E'.structureMap from Over.w g.hom.hom.hom,
      Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, zero_comp_structureMap]
    rfl
  rw [finrank_hom_hom_hom_left, hys, degree_apply]

/-- Composing isogenies of degrees `m` and `n` gives an isogeny of degree `m * n`. -/
theorem IsogenyOfDegree.comp {g : E'.toCommGrp ⟶ E''.toCommGrp} {m n : ℕ}
    (hf : IsogenyOfDegree f m) (hg : IsogenyOfDegree g n) : IsogenyOfDegree (f ≫ g) (m * n) :=
  have := hg.isIsogeny
  ⟨inferInstance, fun s ↦ by rw [degree_comp, hf.degree_eq, hg.degree_eq]⟩

end EllipticCurveGeom

/-! ### Multiplication by an integer over a field -/

namespace EllipticCurveGeom

variable {K : Type u} [Field K] (E : EllipticCurveGeom (Spec (.of K)))

/-- **Over a field, multiplication by a nonzero integer is an isogeny.** -/
theorem isIsogeny_intCast {n : ℤ} (hn : n ≠ 0) : IsIsogeny (n : End E.toCommGrp) where
  isFinite := by simpa using E.isFinite_mulBy_left hn
  flat := by simpa using E.flat_mulBy_left hn
  surjective := by simpa using E.surjective_mulBy_left hn

/-- **Over a field, multiplication by a nonzero integer `n` has degree `n²`** (Katz–Mazur
2.3.1). -/
theorem degree_intCast {n : ℤ} (hn : n ≠ 0) (s : Spec (.of K)) :
    degree (n : End E.toCommGrp) s = n.natAbs ^ 2 := by
  simp [degree_apply, E.finrank_mulBy_left hn]

/-- **Over a field, multiplication by a nonzero integer `n` is an isogeny of degree `n²`.** -/
theorem isogenyOfDegree_intCast {n : ℤ} (hn : n ≠ 0) :
    IsogenyOfDegree (n : End E.toCommGrp) (n.natAbs ^ 2) :=
  ⟨E.isIsogeny_intCast hn, E.degree_intCast hn⟩

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
