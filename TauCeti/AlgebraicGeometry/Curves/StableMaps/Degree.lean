/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableMaps.Category
public import TauCeti.AlgebraicGeometry.Curves.StableMaps.Contracted
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.BaseChange

/-!
# The polarization degree of a prestable map

Let `F : C ⟶ V` be a prestable map over a field `K`, with target `q : V ⟶ Spec K`, and let `a`
be the class of a line bundle `L` on `V`, typically a relatively ample one chosen as a
polarization of the target. The **degree** of `F` with respect to `a` is the degree of the
pullback `F^* L` on the proper curve `C`, and its **degree on a component** `E` of `C` is the degree
of the restriction of `F^* L` to `E`, with its reduced structure:

`deg_a F = deg_K (F^* L)`, `deg_a(F|_E) = deg_K (F^* L|_E)`.

Degrees are the Euler-characteristic degrees `deg L = χ(L) - χ(𝒪)` of
`TauCeti.AlgebraicGeometry.LineBundleClass.eulerDegree`; the degree on a component is the
intersection number `(F^* a · E)` of `TauCeti.AlgebraicGeometry.LineBundleClass.intersectionNumber`.
For a polarization these are the numerical invariants of a stable map: the stability condition
of a map compares the log-canonical degree of a component with three times its polarization
degree, and the decorated dual graph of a stable map records the degree of every component.
The polarization is not part of the data of a prestable map, so it is an argument here. No
ampleness is needed for the results of this file.

A component contracted by `F` has degree zero for every line bundle: the restriction of `F` to
it factors through the spectrum of the residue field of a point of `V`, on which every line bundle
is trivial. So a component of nonzero degree is never contracted. A constant map has degree zero,
in total and on every component. Postcomposing `F` with a morphism of targets `h : V ⟶ W` gives
the degrees of `F` with respect to pulled-back classes `h^* a`.

The total degree is an invariant of the prestable map: isomorphic prestable maps have the same
degree, and the degree does not change under base change along any field extension `L / K`,
because the cohomology of a proper scheme over a field commutes with field extension
(`TauCeti.AlgebraicGeometry.InvertibleSheaf.eulerDegree_pullback`). In particular it is the same
for every geometric fibre.

## Main definitions

In the namespace `TauCeti.AlgebraicGeometry.PrestableMap`:

* `degree K F a`: the degree of `F^* a` on the source curve.
* `componentDegree K F E a`: the degree of `F^* a` on the reduced closed subscheme on `E`, meant
  for the irreducible components `E` of the source curve.

## Main results

In the namespace `TauCeti.AlgebraicGeometry.PrestableMap`:

* `IsContractedComponent.componentDegree_eq_zero`: a contracted component has degree zero.
* `degree_const`, `componentDegree_const`: a constant map has degree zero, in total and on every
  component.
* `degree_postcomp`, `componentDegree_postcomp`: degrees of a postcomposed map.
* `degree_eq_of_iso`: isomorphic prestable maps have the same degree.
* `degree_pullback`: the degree is invariant under extension of the base field.

## References

* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*,
  Proc. Sympos. Pure Math. 62 (1997), Part 2, 45–96, Section 1, for the degree of a stable map
  with respect to a polarization and the stability criterion that uses it.
* K. Behrend and Yu. Manin, *Stacks of stable maps and Gromov–Witten invariants*,
  Duke Math. J. 85 (1996), 1–60, Section 1, for the degrees decorating the components of a
  stable map.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

namespace PrestableMap

variable (K : Type u) [Field K] {V W : Scheme.{u}} {q : V ⟶ Spec (.of K)} {n : ℕ}
  (F : PrestableMap q n)

/-! ### The total degree -/

/-- The **degree** of a prestable map `F` over a field `K` with respect to the class `a` of a line
bundle `L` on the target: the Euler-characteristic degree over `K` of `F^* L` on the source curve.
When `L` is a polarization of the target, this is the degree of the map. -/
def degree (a : LineBundleClass V) : ℤ :=
  LineBundleClass.intersectionNumber K F.map a

/-- The degree of `F` with respect to `a` is the degree of the pulled-back class `F^* a`. -/
lemma degree_def (a : LineBundleClass V) :
    F.degree K a = LineBundleClass.eulerDegree K (LineBundleClass.pullback F.map a) :=
  LineBundleClass.intersectionNumber_def K F.map a

/-- The trivial class has degree zero. -/
@[simp]
lemma degree_one : F.degree K 1 = 0 :=
  LineBundleClass.intersectionNumber_one K F.map

/-- The degree of a postcomposed map `F ≫ h` with respect to `a` is the degree of `F` with respect
to the pulled-back class `h^* a`. -/
@[simp]
lemma degree_postcomp {r : W ⟶ Spec (.of K)} (h : V ⟶ W) (hh : h ≫ r = q)
    (a : LineBundleClass W) :
    (F.postcomp h hh).degree K a = F.degree K (LineBundleClass.pullback h a) :=
  -- The source curve of `F.postcomp h hh` is that of `F`, and its map is `F.map ≫ h`
  -- (`postcomp_curve`, `postcomp_map`).
  (LineBundleClass.intersectionNumber_pullback K F.map h a).symm

/-- **A constant map has degree zero.** -/
@[simp]
lemma degree_const (P : PointedPrestableFamily (Spec (.of K)) n) (σ : Spec (.of K) ⟶ V)
    (hσ : σ ≫ q = 𝟙 _) (a : LineBundleClass V) :
    (const P σ hσ).degree K a = 0 :=
  LineBundleClass.intersectionNumber_eq_zero_of_eq_comp K _ P.toBase σ (const_map P σ hσ)
    IsLocalRing.specializes_closedPoint a

/-- **Isomorphic prestable maps have the same degree.** -/
theorem degree_eq_of_iso {G : PrestableMap q n} (e : F ≅ G) (a : LineBundleClass V) :
    F.degree K a = G.degree K a := by
  -- `e` gives an isomorphism of source curves over `Spec K`.
  rw [degree_def, degree_def, ← e.hom.hom_comp_map, ← LineBundleClass.pullback_comp]
  exact LineBundleClass.eulerDegree_pullback_of_isIso e.hom.curve.hom (by simp) _

/-- **The degree is invariant under extension of the base field.** The degree over a field
extension `L` of `K` of the base change of `F` to `L`, with respect to the pullback of `a` to the
base-changed target, is the degree of `F` with respect to `a`. -/
theorem degree_pullback {L : Type u} [Field L] [Algebra K L] (a : LineBundleClass V) :
    (F.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).degree L
        (LineBundleClass.pullback (Limits.pullback.fst q _) a) =
      F.degree K a := by
  -- The source curve of the base change is the fibre product `C ×_K L`.
  have H : IsPullback (Limits.pullback.fst F.curve.toBase _)
      ((F.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).curve.total ↘ Spec (.of L))
      (F.curve.total ↘ Spec (.of K)) (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    IsPullback.of_hasPullback _ _
  rw [degree_def, degree_def,
    ← LineBundleClass.eulerDegree_pullback (Y := (F.pullback _).curve.total) H,
    LineBundleClass.pullback_comp, pullback_map_fst]
  exact congrArg _ (LineBundleClass.pullback_comp _ _ a).symm

/-! ### The degree on a component -/

/-- The **degree on a component** `E` of a prestable map `F` over a field `K` with respect to the
class `a` of a line bundle `L` on the target: the degree over `K` of the restriction of `F^* L` to
the reduced induced closed subscheme on `E`, that is, the intersection number `(F^* a · E)`. It is
meant for the irreducible components `E` of the source curve. -/
def componentDegree (E : Closeds F.curve.total) (a : LineBundleClass V) : ℤ :=
  LineBundleClass.intersectionNumber K ((Scheme.IdealSheafData.vanishingIdeal E).subschemeι ≫ F.map)
    a

/-- The degree on `E` is the intersection number of `a` with the reduced closed subscheme on `E`,
mapped to the target by `F`. -/
lemma componentDegree_def (E : Closeds F.curve.total) (a : LineBundleClass V) :
    F.componentDegree K E a = LineBundleClass.intersectionNumber K
      ((Scheme.IdealSheafData.vanishingIdeal E).subschemeι ≫ F.map) a :=
  (rfl)

/-- The trivial class has degree zero on every component. -/
@[simp]
lemma componentDegree_one (E : Closeds F.curve.total) : F.componentDegree K E 1 = 0 :=
  LineBundleClass.intersectionNumber_one K _

/-- The degree on `E` of a postcomposed map `F ≫ h` with respect to `a` is the degree on `E` of
`F` with respect to the pulled-back class `h^* a`. -/
@[simp]
lemma componentDegree_postcomp {r : W ⟶ Spec (.of K)} (h : V ⟶ W) (hh : h ≫ r = q)
    (E : Closeds F.curve.total) (a : LineBundleClass W) :
    (F.postcomp h hh).componentDegree K E a =
      F.componentDegree K E (LineBundleClass.pullback h a) :=
  calc (F.postcomp h hh).componentDegree K E a
      = LineBundleClass.intersectionNumber K
          ((Scheme.IdealSheafData.vanishingIdeal E).subschemeι ≫ F.map ≫ h) a :=
      -- The source curve of `F.postcomp h hh` is that of `F`, and its map is `F.map ≫ h`
      -- (`postcomp_curve`, `postcomp_map`).
      (rfl)
    _ = F.componentDegree K E (LineBundleClass.pullback h a) := by
      rw [componentDegree_def, LineBundleClass.intersectionNumber_pullback, Category.assoc]

/-- **A contracted component has degree zero.** If the prestable map `F` over a field, with target
locally of finite type, contracts the irreducible component `E`, then every line-bundle class has
degree zero on `E`. Hence a component of nonzero degree, for instance of positive degree with
respect to a polarization, is never contracted. -/
theorem IsContractedComponent.componentDegree_eq_zero [LocallyOfFiniteType q]
    {E : Closeds F.curve.total} (hE : F.IsContractedComponent E) (a : LineBundleClass V) :
    F.componentDegree K E a = 0 := by
  -- The restriction of `F` to `E` factors through `Spec κ(v)` for a point `v` of the target.
  obtain ⟨v, g, hg⟩ :=
    (F.isContractedComponent_iff_exists_subschemeι_comp_eq hE.mem_irreducibleComponents).mp hE
  exact LineBundleClass.intersectionNumber_eq_zero_of_eq_comp K _ g _ hg
    IsLocalRing.specializes_closedPoint a

/-- **A constant map has degree zero on every component.** -/
@[simp]
lemma componentDegree_const (P : PointedPrestableFamily (Spec (.of K)) n)
    (σ : Spec (.of K) ⟶ V) (hσ : σ ≫ q = 𝟙 _) (E : Closeds P.total) (a : LineBundleClass V) :
    (const P σ hσ).componentDegree K E a = 0 :=
  LineBundleClass.intersectionNumber_eq_zero_of_eq_comp K _
    ((Scheme.IdealSheafData.vanishingIdeal E).subschemeι ≫ P.toBase) σ
    -- The source curve of the constant map is `P` and its map is `P.toBase ≫ σ` (`const_curve`,
    -- `const_map`), so this is associativity.
    (Category.assoc _ _ _).symm
    IsLocalRing.specializes_closedPoint a

end PrestableMap

end TauCeti.AlgebraicGeometry
