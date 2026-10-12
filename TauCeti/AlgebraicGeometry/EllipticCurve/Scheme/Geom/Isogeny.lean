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
import TauCeti.AlgebraicGeometry.GroupScheme.KilledByRank
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank

/-!
# Isogenies of elliptic curves over a scheme and their degree

Let `E` and `E'` be elliptic curves over a scheme `S`. A homomorphism `f : E ⟶ E'` of elliptic
curves over `S` (a morphism `E.toCommGrp ⟶ E'.toCommGrp` of commutative group schemes) is an
**isogeny** when its underlying morphism of schemes is finite locally free (finite, flat and locally
of finite presentation) and surjective (`EllipticCurveGeom.IsIsogeny`).

The rank of a finite locally free morphism is a locally constant function on its target. For an
isogeny it is constant along the fibres of `E' ⟶ S`, since translations of `E'` by points in the
image of `f` preserve it (`TauCeti.GroupScheme.finrank_left_eq`). It is therefore a function on
the base, the **degree** of `f` (`EllipticCurveGeom.degree`): at `s ∈ S`, the rank of `f` at the
zero of the fibre over `s`. The degree is locally constant and positive, but over a disconnected
base it need not be constant; a statement about an isogeny of a single degree `n` assumes
`∀ s, degree f s = n`.

The kernel `ker f` of an isogeny is a finite locally free commutative group scheme over `S`
(`EllipticCurveGeom.IsIsogeny.kernel`), whose rank at `s` is the degree of `f` at `s`. By Deligne's
theorem it is killed by the degree: if `f` has degree `n`, every point of `E` killed by `f` is
killed by `n` (`EllipticCurveGeom.IsIsogeny.pow_eq_one`). This is the input for factoring `[n]`
through the quotient of `E` by `ker f`, which is how the dual isogeny is constructed.

Isomorphisms are the isogenies of degree one, and isogenies compose, with degrees multiplying.
Over a field, multiplication by a nonzero integer `n` is an isogeny of degree `n²`.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsIsogeny f`: the homomorphism `f` is an isogeny.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.degree f`: the degree of `f`, a function `S → ℕ`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsIsogeny.kernel f`: the kernel of an isogeny, as a
  finite locally free commutative group scheme over `S`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.finrank_hom_hom_hom_left`: the rank of an isogeny at
  a point of `E'` over `s` is the degree at `s`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isLocallyConstant_degree` and
  `TauCeti.AlgebraicGeometry.EllipticCurveGeom.degree_pos`: the degree of an isogeny is locally
  constant and positive.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsIsogeny.finrank_kernel`: the rank of `ker f` is the
  degree.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.IsIsogeny.pow_eq_one`: an isogeny of degree `n`
  kills only points killed by `n`.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isIso_iff_degree_eq_one`: an isogeny is an
  isomorphism exactly when it has degree one; in particular an isomorphism has degree one
  (`TauCeti.AlgebraicGeometry.EllipticCurveGeom.degree_eq_one_of_isIso`).
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.degree_comp`: degrees multiply under composition.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.degree_intCast`: over a field, multiplication by a
  nonzero integer `n` is an isogeny of degree `n²`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §2.4 and 2.3.1.
* P. Deligne, letter quoted in J. Tate and F. Oort, *Group schemes of prime order*, Ann. Sci.
  École Norm. Sup. (4) 3 (1970), 1–21, for the killing of a finite locally free commutative group
  scheme by its rank.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S : Scheme.{u}} {E E' E'' : EllipticCurveGeom S}

/-! ### Isogenies -/

/-- **Isogenies of elliptic curves.** A homomorphism `f : E ⟶ E'` of elliptic curves over `S` is an
isogeny when its underlying morphism of schemes is finite locally free, that is finite, flat and
locally of finite presentation, and surjective (Katz–Mazur §2.4). -/
class IsIsogeny (f : E.toCommGrp ⟶ E'.toCommGrp) : Prop where
  /-- The underlying morphism of schemes is finite. -/
  isFinite : IsFinite f.hom.hom.hom.left
  /-- The underlying morphism of schemes is flat. -/
  flat : Flat f.hom.hom.hom.left
  /-- The underlying morphism of schemes is locally of finite presentation. -/
  locallyOfFinitePresentation : LocallyOfFinitePresentation f.hom.hom.hom.left
  /-- The underlying morphism of schemes is surjective. -/
  surjective : Surjective f.hom.hom.hom.left

attribute [instance] IsIsogeny.isFinite IsIsogeny.flat IsIsogeny.locallyOfFinitePresentation
  IsIsogeny.surjective

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

variable (f : E.toCommGrp ⟶ E'.toCommGrp) [IsIsogeny f]

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

/-- An isogeny has constant degree `n` exactly when its underlying morphism of schemes has constant
rank `n`. -/
theorem forall_finrank_hom_hom_hom_left_eq_iff {n : ℕ} :
    (∀ y, f.hom.hom.hom.left.finrank y = n) ↔ ∀ s, degree f s = n := by
  refine ⟨fun h s ↦ h _, fun h y ↦ by rw [finrank_hom_hom_hom_left, h]⟩

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
      ‹IsIsogeny f›.locallyOfFinitePresentation
    inferInstance

/-- **The rank of the kernel of an isogeny is its degree.** -/
theorem IsIsogeny.finrank_kernel (s : S) :
    (IsIsogeny.kernel f).structureMap.finrank s = degree f s := by
  have : IsFinite (Grp.ofHom f.hom.hom.hom).hom.hom.left := ‹IsIsogeny f›.isFinite
  have : Flat (Grp.ofHom f.hom.hom.hom).hom.hom.left := ‹IsIsogeny f›.flat
  rw [degree_apply, ← one_left]
  exact GroupScheme.finrank_kernel_hom (Grp.ofHom f.hom.hom.hom) s

/-- **The kernel of an isogeny is killed by its degree** (Deligne's theorem). If the isogeny
`f : E ⟶ E'` has degree `n` at every point of `S`, then every point `x` of `E`, with values in any
`Z` over `S`, that is killed by `f` is killed by `n`: `n x = 0`, written `x ^ n = 1` for the
multiplicative group law on points. -/
theorem IsIsogeny.pow_eq_one {n : ℕ} (hn : ∀ s, degree f s = n) {Z : Over S}
    (x : Z ⟶ Over.mk E.structureMap) (hx : x ≫ f.hom.hom.hom = 1) : x ^ n = 1 := by
  let g := Grp.ofHom f.hom.hom.hom
  have hy : GroupScheme.kernelLift (f := g) x hx ^ n = 1 :=
    (IsIsogeny.kernel f).pow_eq_one_of_finrank (fun s ↦ (finrank_kernel f s).trans (hn s)) _
  calc x ^ n = (GroupScheme.kernelLift (f := g) x hx ≫ (Limits.kernel.ι g).hom.hom) ^ n :=
        congrArg (· ^ n) (GroupScheme.kernelLift_ι (f := g) x hx).symm
    _ = (GroupScheme.kernelLift (f := g) x hx ^ n) ≫ (Limits.kernel.ι g).hom.hom :=
        (MonObj.pow_comp _ _ _).symm
    _ = 1 := by rw [hy, MonObj.one_comp]

/-- **An isogeny is an isomorphism exactly when it has degree one.** -/
theorem isIso_iff_degree_eq_one : IsIso f ↔ ∀ s, degree f s = 1 := by
  rw [isIso_iff_isIso_hom_hom_hom_left, Scheme.Hom.isIso_iff_finrank_eq, funext_iff,
    ← forall_finrank_hom_hom_hom_left_eq_iff]
  simp only [Pi.one_apply]

/-- An isomorphism of elliptic curves has degree one. -/
@[simp]
theorem degree_eq_one_of_isIso (f : E.toCommGrp ⟶ E'.toCommGrp) [IsIso f] (s : S) :
    degree f s = 1 :=
  (isIso_iff_degree_eq_one f).mp ‹_› s

/-- **Degrees multiply under composition.** If the isogeny `f : E ⟶ E'` has degree `n` at every
point of `S`, then the degree of its composite with an isogeny `g : E' ⟶ E''` is `n` times the
degree of `g`. -/
theorem degree_comp (g : E'.toCommGrp ⟶ E''.toCommGrp) [IsIsogeny g] {n : ℕ}
    (hn : ∀ s, degree f s = n) (s : S) : degree (f ≫ g) s = n * degree g s := by
  have h : (f ≫ g).hom.hom.hom.left = f.hom.hom.hom.left ≫ g.hom.hom.hom.left := by simp
  rw [degree_apply, degree_apply, h]
  exact Scheme.Hom.finrank_comp _ _ ((forall_finrank_hom_hom_hom_left_eq_iff f).mpr hn) _

end EllipticCurveGeom

/-! ### Multiplication by an integer over a field -/

namespace EllipticCurveGeom

variable {K : Type u} [Field K] (E : EllipticCurveGeom (Spec (.of K)))

/-- **Over a field, multiplication by a nonzero integer is an isogeny.** -/
theorem isIsogeny_intCast {n : ℤ} (hn : n ≠ 0) : IsIsogeny (n : End E.toCommGrp) where
  isFinite := by simpa using E.isFinite_mulBy_left hn
  flat := by simpa using E.flat_mulBy_left hn
  locallyOfFinitePresentation := by
    -- `E` is of finite type over a field, hence locally noetherian
    have : IsLocallyNoetherian (Over.mk E.structureMap).left :=
      LocallyOfFiniteType.isLocallyNoetherian E.structureMap
    have := E.isFinite_mulBy_left hn
    simp only [intCast_hom_hom_hom]
    infer_instance
  surjective := by simpa using E.surjective_mulBy_left hn

/-- **Over a field, multiplication by a nonzero integer `n` has degree `n²`** (Katz–Mazur
2.3.1). -/
theorem degree_intCast {n : ℤ} (hn : n ≠ 0) (s : Spec (.of K)) :
    degree (n : End E.toCommGrp) s = n.natAbs ^ 2 := by
  simp [degree_apply, E.finrank_mulBy_left hn]

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
