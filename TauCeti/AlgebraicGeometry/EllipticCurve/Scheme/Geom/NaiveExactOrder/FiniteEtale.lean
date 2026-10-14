/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.NaiveExactOrder.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion.Etale.Locus
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Rank
import TauCeti.AlgebraicGeometry.EqualizerCarrier
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The finite étale cover of points of naive exact order

For an elliptic curve `E/S` and a natural number `N` invertible on `S`, the scheme
`naiveExactOrderOpens E hN` represents points of naive exact order `N`. Its inclusion in
`E[N]` is both open and closed, so its structural morphism is finite étale. It is also
surjective: every geometric fibre has a point of exact order `N`.

Thus a point of naive exact order can be chosen after a finite étale surjective base change.
This cover is the relative parameter scheme for the naive single-point level problem.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 1.4.4 and §3.7.
* D. Loeffler, *Modular Curves*, lecture notes, Proposition 3.8.2.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S) {N : ℕ}
  (hN : ∀ s : S, (N : S.residueField s) ≠ 0)

/-- When `N` is invertible on the base, the exact-order locus is a closed subscheme of `E[N]`
as well as an open subscheme. -/
instance isClosedImmersion_naiveExactOrderOpens_ι :
    IsClosedImmersion (E.naiveExactOrderOpens hN).ι := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [Scheme.Opens.range_ι, coe_naiveExactOrderOpens]
  exact (E.isClopen_naiveExactOrderLocus hN).isClosed

/-- The scheme of points of naive exact order `N` is finite over the base when `N` is
invertible on the base. -/
instance isFinite_naiveExactOrderOpens :
    IsFinite ((E.naiveExactOrderOpens hN).ι ≫ (E.torsion N).X.hom) := by
  rcases isEmpty_or_nonempty S with hS | ⟨⟨s⟩⟩
  · have : IsEmpty (E.naiveExactOrderOpens hN : Scheme) :=
      Function.isEmpty ((E.naiveExactOrderOpens hN).ι ≫ (E.torsion N).X.hom)
    infer_instance
  have hN₀ : (N : ℤ) ≠ 0 := by
    exact_mod_cast (fun h : N = 0 ↦ hN s (by simp [h]))
  have := E.isFinite_torsion_hom hN₀
  infer_instance

/-- The scheme of points of naive exact order `N` is étale over the base when `N` is
invertible on the base. -/
instance etale_naiveExactOrderOpens :
    Etale ((E.naiveExactOrderOpens hN).ι ≫ (E.torsion N).X.hom) := by
  have := E.etale_torsion_hom_of_forall_intCast_ne_zero (n := N) (by
    intro s
    exact_mod_cast hN s)
  infer_instance

section SepClosed

variable {K : Type u} [Field K] [IsSepClosed K]
  (E : EllipticCurveGeom (Spec (.of K)))

/-- Over a separably closed field where `N` is invertible, an elliptic curve has a point of
naive exact order `N`. -/
theorem exists_isOfNaiveExactOrder (hN : (N : K) ≠ 0) :
    ∃ P : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E.structureMap, E.IsOfNaiveExactOrder P N := by
  obtain ⟨φ, hφ⟩ := E.exists_isFiberwiseInjective hN
  let i : Multiplicative (ZMod N) →* Multiplicative (ZMod N × ZMod N) :=
    (AddMonoidHom.inl (ZMod N) (ZMod N)).toMultiplicative
  have hi : Function.Injective i := fun a b h ↦
    Multiplicative.toAdd.injective (congrArg Prod.fst (congrArg Multiplicative.toAdd h))
  exact ⟨_, E.isFiberwiseInjective_iff_isOfNaiveExactOrder.mp (hφ.comp hi)⟩

end SepClosed

/-- For a geometric point of the base in a characteristic prime to `N`, there is a point
of naive exact order `N` above it, valued in the same separably closed field. -/
theorem exists_isOfNaiveExactOrder_over {K : Type u} [Field K] [IsSepClosed K]
    (t : Spec (.of K) ⟶ S) (hN : (N : K) ≠ 0) :
    ∃ P : Over.mk t ⟶ Over.mk E.structureMap, E.IsOfNaiveExactOrder P N := by
  let E' := E.baseChange t
  let g := (E.baseChangeIso t).hom ≫ pullback.fst E.structureMap t
  have hg : IsPullback g E'.structureMap E.structureMap t := E.isPullback_baseChange t
  have h0 : E'.zero ≫ g = t ≫ E.zero := by simp [E', g]
  obtain ⟨P, hP⟩ := E'.exists_isOfNaiveExactOrder hN
  -- View a point of the geometric fibre as a `K`-valued point of `E` over `S`.
  let φ : (𝟙_ (Over (Spec (.of K))) ⟶ Over.mk E'.structureMap) →*
      (Over.mk t ⟶ Over.mk E.structureMap) :=
    { toFun P := Over.homMk (P.left ≫ g) (by simp [Category.assoc, hg.w])
      map_one' := by ext1; simp [hom_one_left, h0]
      map_mul' P Q := by
        ext1
        simp only [Over.homMk_left]
        rw [mul_left_comp_of_isPullback hg h0, hom_mul_left]
        simp only [Over.homMk_left]
        rfl }
  have hφ : Function.Injective φ := by
    intro P Q h
    ext1
    apply hg.hom_ext
    · exact congrArg CommaMorphism.left h
    · simp
  have hQ : E.IsOfNaiveExactOrder (φ P) N := by
    apply isOfNaiveExactOrder_iff.mpr
    refine ⟨by rw [← map_pow, hP.pow_eq_one, map_one], fun d hd hdN ↦ ?_⟩
    -- A nonempty closed subscheme of `Spec K` is all of `Spec K`.
    by_contra! h
    have : Nonempty (equalizer (φ P ^ d) 1).left := h
    have : Subsingleton (Over.mk t).left :=
      inferInstanceAs (Subsingleton (Spec (.of K)))
    have : IsReduced (Over.mk t).left :=
      inferInstanceAs (IsReduced (Spec (.of K)))
    have : IsSeparated (Over.mk E.structureMap).hom :=
      inferInstanceAs (IsSeparated E.structureMap)
    have : Surjective (equalizer.ι (φ P ^ d) 1).left :=
      ⟨Function.surjective_to_subsingleton _⟩
    have : IsIso (equalizer.ι (φ P ^ d) 1).left :=
      isIso_of_isClosedImmersion_of_surjective _
    have : IsIso ((Over.forget S).map (equalizer.ι (φ P ^ d) 1)) :=
      inferInstanceAs (IsIso (equalizer.ι (φ P ^ d) 1).left)
    have : IsIso (equalizer.ι (φ P ^ d) 1) :=
      isIso_of_reflects_iso _ (Over.forget S)
    have heq : φ P ^ d = 1 :=
      (cancel_epi (equalizer.ι (φ P ^ d) 1)).mp (equalizer.condition _ _)
    have hPd : P ^ d = 1 := hφ (by simpa using heq)
    exact (isEmpty_equalizer_iff_ne _ _).mp (hP.isEmpty_equalizer hd hdN) hPd
  exact ⟨φ P, hQ⟩

/-- Every geometric fibre of the finite étale exact-order scheme has a point, so its
structural morphism is surjective. -/
instance surjective_naiveExactOrderOpens :
    Surjective ((E.naiveExactOrderOpens hN).ι ≫ (E.torsion N).X.hom) := by
  refine ⟨fun s ↦ ?_⟩
  let L := AlgebraicClosure (S.residueField s)
  let t : Spec (.of L) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) L)) ≫ S.fromSpecResidueField s
  have hNL : (N : L) ≠ 0 := by
    rw [← map_natCast (algebraMap (S.residueField s) L)]
    exact (map_ne_zero_iff _ (algebraMap (S.residueField s) L).injective).mpr (hN s)
  obtain ⟨P, hP⟩ := E.exists_isOfNaiveExactOrder_over t hNL
  let u := (E.naiveExactOrderRepresentableBy hN).homEquiv.symm
    ⟨P, mem_naiveExactOrderSubfunctor_obj.mpr hP⟩
  obtain ⟨a⟩ : Nonempty (Spec (.of L)) := inferInstance
  refine ⟨u.left a, ?_⟩
  have hu : u.left ≫ (E.naiveExactOrderOpens hN).ι ≫ (E.torsion N).X.hom = t := Over.w u
  rw [← Scheme.Hom.comp_apply, hu]
  exact Scheme.fromSpecResidueField_apply s _

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
