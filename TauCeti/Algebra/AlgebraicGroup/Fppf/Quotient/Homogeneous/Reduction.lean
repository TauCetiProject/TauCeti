/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Scheme
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Sites.RegularEpi

/-!
# Reductions of the trivial torsor

For an affine group `G`, a closed subgroup `N` and a test sheaf `S`, a reduction of the
trivial right `G`-torsor is an `N`-subtorsor of `S × G`. Its sections above a point of
`S` form a left coset whenever there is a lift, and lifts exist fppf locally.

`CommHopfAlgCat.fppfHomogeneousQuotientReductionEquiv` identifies maps `S ⟶ G/N`
with these embedded torsors. The map corresponding to a reduction sends each local
lift to its coset. The fibre criterion `fppfHomogeneousQuotientProjection_app_eq_iff`
makes the coset constant along the fibres of the subtorsor projection, so it descends
by `CategoryTheory.EffectiveEpi.desc`. The classification applies to the sheaf of points
of a test scheme without any choice of global representative.
For a representing scheme, `CommHopfAlgCat.representedQuotientReductionEquiv` expresses
membership by equality of two scheme morphisms into the quotient.
-/

public section

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R] (H : CommHopfAlgCat.{u} R) (I : HopfIdeal R H)
  (S : Sheaf (CommAlgCat.fppfTopology R) (Type (u + 1)))

/-- A reduction of the trivial right torsor over `S` to the closed subgroup defined by `I`.
The carrier is a subsheaf of `S × G`. Its projection has local sections and each nonempty
fibre is a left coset of the subgroup of points. -/
@[ext]
structure FppfTorsorReduction where
  /-- Pairs consisting of a base point and a group point in the subtorsor. -/
  carrier : Subfunctor (S.obj ⊗ (HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u}))
  /-- The embedded torsor satisfies fppf descent. -/
  isSheaf : Presheaf.IsSheaf (CommAlgCat.fppfTopology R) carrier.toFunctor
  /-- Every base point has a lift fppf locally. -/
  locallySurjective : Presheaf.IsLocallySurjective (CommAlgCat.fppfTopology R)
    (carrier.ι ≫ fst _ _)
  /-- The fibre through `g` consists of exactly its right translates by subgroup points. -/
  mem_iff {A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ} {s : S.obj.obj A}
    {g : HopfAlgebra.points (R := R) (H := H) A.unop.unop}
    (hg : (s, ULift.up g) ∈ carrier.obj A)
    (g' : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    (s, ULift.up g') ∈ carrier.obj A ↔ g⁻¹ * g' ∈ quotientPointsSubgroup H I A.unop.unop

private theorem isSheaf_torsorProduct :
    Presieve.IsSheaf (CommAlgCat.fppfTopology R)
      (S.obj ⊗ (HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u})) :=
  (isSheaf_iff_isSheaf_of_type _ _).mp (Sheaf.tensorProd_isSheaf _ S
    ⟨_, (isSheaf_iff_isSheaf_of_type _ _).mpr
      ((Presieve.isSheaf_comp_uliftFunctor_iff _).mpr
        ((isSheaf_iff_isSheaf_of_type _ _).mp (HopfAlgebra.pointsPresheaf_isSheaf H)))⟩)

variable {S}

/-- Pull back the quotient projection along a map to the homogeneous quotient. A pair
`(s, g)` belongs to the resulting reduction precisely when `g` lifts the image of `s`. -/
private noncomputable def fppfTorsorReductionOfHom (f : S ⟶ fppfHomogeneousQuotient H I) :
    FppfTorsorReduction H I S := by
  let q := fppfHomogeneousQuotientProjection H I
  let P : Subfunctor (S.obj ⊗ (HopfAlgebra.pointsPresheaf H ⋙ uliftFunctor.{u + 1, u})) :=
    { obj := fun A ↦ {p | q.app A p.2 = f.hom.app A p.1}
      map := by
        rintro A B i ⟨s, g⟩ h
        exact (q.naturality_apply i g).trans
          ((congrArg ((fppfHomogeneousQuotient H I).obj.map i) h).trans
            (f.hom.naturality_apply i s).symm) }
  refine ⟨P, ?_, ⟨fun {U} s ↦ ?_⟩, ?_⟩
  · rw [isSheaf_iff_isSheaf_of_type, P.isSheaf_iff (isSheaf_torsorProduct H S)]
    intro A p h
    refine (((isSheaf_iff_isSheaf_of_type _ _).mp (fppfHomogeneousQuotient H I).property)
      _ h).isSeparatedFor.ext fun B i hi ↦ ?_
    exact (q.naturality_apply i.op p.2).symm.trans (hi.trans (f.hom.naturality_apply i.op p.1))
  · refine (CommAlgCat.fppfTopology R).superset_covering ?_
      (Presheaf.imageSieve_mem _ q (f.hom.app _ s))
    rintro V i ⟨g, hg⟩
    exact ⟨⟨(S.obj.map i.op s, g), hg.trans (f.hom.naturality_apply i.op s).symm⟩, rfl⟩
  · intro A s g hg g'
    have h : q.app A (ULift.up g) = f.hom.app A s := hg
    -- Express membership in the pullback by the equality defining its carrier.
    change q.app A (ULift.up g') = f.hom.app A s ↔ _
    rw [← h, eq_comm]
    exact fppfHomogeneousQuotientProjection_app_eq_iff H I A g g'

namespace FppfTorsorReduction

variable {H I} (P : FppfTorsorReduction H I S)

/-- An inclusion of reductions to the same subgroup over the same base is an equality. -/
theorem eq_of_le {P' : FppfTorsorReduction H I S} (h : P.carrier ≤ P'.carrier) : P = P' := by
  apply FppfTorsorReduction.ext
  apply le_antisymm h
  rintro A ⟨s, g⟩ hg
  apply (P.carrier.isSheaf_iff (isSheaf_torsorProduct H S)).mp
    ((isSheaf_iff_isSheaf_of_type _ _).mp P.isSheaf)
  let π := P.carrier.ι ≫ fst _ _
  have : Presheaf.IsLocallySurjective (CommAlgCat.fppfTopology R) π := P.locallySurjective
  refine (CommAlgCat.fppfTopology R).superset_covering ?_ (Presheaf.imageSieve_mem _ π s)
  rintro B i ⟨⟨⟨t, k⟩, hk⟩, ht⟩
  -- The first projection of a pair in the subtorsor is its base point.
  change t = S.obj.map i.op s at ht
  subst t
  exact (P.mem_iff hk _).2 ((P'.mem_iff (h _ hk) _).1 (P'.carrier.map i.op hg))

/-- The cosets of local lifts in a reduction descend to a unique map to the quotient. -/
private theorem existsUnique_hom :
    ∃! f : S ⟶ fppfHomogeneousQuotient H I,
      ∀ (A) (p : P.carrier.toFunctor.obj A),
        (fppfHomogeneousQuotientProjection H I).app A p.val.2 = f.hom.app A p.val.1 := by
  let T : Sheaf (CommAlgCat.fppfTopology R) (Type (u + 1)) := ⟨_, P.isSheaf⟩
  let π : T ⟶ S := ⟨P.carrier.ι ≫ fst _ _⟩
  let q : T ⟶ fppfHomogeneousQuotient H I :=
    ⟨P.carrier.ι ≫ snd _ _ ≫ fppfHomogeneousQuotientProjection H I⟩
  have : Sheaf.IsLocallySurjective π := P.locallySurjective
  have := IsRegularEpiCategory.regularEpiOfEpi π
  have compat {Z} (a b : Z ⟶ T) (hab : a ≫ π = b ≫ π) : a ≫ q = b ≫ q := by
    ext A z
    let x := a.hom.app A z
    let y := b.hom.app A z
    have hxy : x.val.1 = y.val.1 := congrArg (fun k ↦ k.hom.app A z) hab
    have hy : (x.val.1, y.val.2) ∈ P.carrier.obj A := hxy ▸ y.property
    exact (fppfHomogeneousQuotientProjection_app_eq_iff H I A _ _).2
      ((P.mem_iff x.property _).1 hy)
  refine ⟨EffectiveEpi.desc π q compat, fun A p ↦ ?_, fun f hf ↦ ?_⟩
  · exact congrArg (fun k ↦ k.hom.app A p) (EffectiveEpi.fac π q compat).symm
  · apply EffectiveEpi.uniq π q compat
    ext A p
    exact (hf A p).symm

end FppfTorsorReduction

/-- Maps `S ⟶ G/N` classify reductions of the trivial `G`-torsor over `S` to `N`.
The equivalence takes a map to its sheaf of lifts to `G`. -/
noncomputable def fppfHomogeneousQuotientReductionEquiv :
    (S ⟶ fppfHomogeneousQuotient H I) ≃ FppfTorsorReduction H I S :=
  Equiv.ofBijective (fppfTorsorReductionOfHom H I) <| by
    constructor
    · intro f g h
      apply (fppfTorsorReductionOfHom H I f).existsUnique_hom.unique
      · exact fun _ p ↦ p.property
      · intro A p
        have hp : p.val ∈ (fppfTorsorReductionOfHom H I g).carrier.obj A := h ▸ p.property
        exact hp
    · intro P
      obtain ⟨f, hf, -⟩ := P.existsUnique_hom
      exact ⟨f, (P.eq_of_le fun A p hp ↦ hf A ⟨p, hp⟩).symm⟩

/-- The reduction classified by a map consists of the pairs `(s, g)` with image of `g`
equal to the value of the map at `s`. -/
@[simp]
theorem mem_fppfHomogeneousQuotientReductionEquiv_iff (f : S ⟶ fppfHomogeneousQuotient H I)
    {A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ} (s : S.obj.obj A)
    (g : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    (s, ULift.up g) ∈ (fppfHomogeneousQuotientReductionEquiv H I f).carrier.obj A ↔
      (fppfHomogeneousQuotientProjection H I).app A (ULift.up g) = f.hom.app A s :=
  Iff.rfl

/-- A group point represents the value of the classifying map at `s` exactly when it
belongs to the given reduction above `s`. -/
@[simp]
theorem projection_eq_fppfHomogeneousQuotientReductionEquiv_symm_app_iff
    (P : FppfTorsorReduction H I S) {A : ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ} (s : S.obj.obj A)
    (g : HopfAlgebra.points (R := R) (H := H) A.unop.unop) :
    dsimp% (fppfHomogeneousQuotientProjection H I).app A (ULift.up g) =
        ((fppfHomogeneousQuotientReductionEquiv H I).symm P).hom.app A s ↔
      (s, ULift.up g) ∈ P.carrier.obj A := by
  rw [← mem_fppfHomogeneousQuotientReductionEquiv_iff, Equiv.apply_symm_apply]
  exact Iff.rfl

open AlgebraicGeometry

variable {X : Over (Spec (CommRingCat.of R))}
  (e : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)

/-- Points of a represented homogeneous quotient with values in any test scheme `Y` are
reductions of its trivial torsor. -/
noncomputable def representedQuotientReductionEquiv (Y : Over (Spec (CommRingCat.of R))) :
    (Y ⟶ X) ≃ FppfTorsorReduction H I (CommAlgCat.pointsSheaf Y) :=
  (CommAlgCat.fullyFaithfulPointsSheafFunctor R).homEquiv.trans
    (e.homToEquiv.symm.trans (fppfHomogeneousQuotientReductionEquiv H I))

/-- Over an affine point `s` of the test scheme, a group point `g` belongs to the reduction
of `f` exactly when its quotient projection is the composite of `s` with `f`. -/
@[simp]
theorem mem_representedQuotientReductionEquiv_iff {Y : Over (Spec (CommRingCat.of R))}
    (f : Y ⟶ X) {A : CommAlgCat.{u} R} (s : (algSpec (CommRingCat.of R)).obj (op A) ⟶ Y)
    (g : HopfAlgebra.points (R := R) (H := H) A) :
    (ULift.up s, ULift.up g) ∈ ((representedQuotientReductionEquiv H I e Y f).carrier.obj
      (op (op A))) ↔ Spec.mapMulEquiv g ≫ representedQuotientProjection H I e = s ≫ f := by
  let φ := (CommAlgCat.pointsSheafFunctor R).map f ≫ e.inv
  refine (mem_fppfHomogeneousQuotientReductionEquiv_iff H I φ (A := op (op A))
    (ULift.up s) g).trans ?_
  rw [mapMulEquiv_comp_representedQuotientProjection]
  let i := ((sheafToPresheaf _ _).mapIso e).app (op (op A))
  exact i.toEquiv.eq_symm_apply.trans ULift.ext_iff

end CommHopfAlgCat
