/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import TauCeti.Algebra.Homology.DerivedCategory.KProjective

/-!
# Morphisms from a projective object placed in one degree

Let `P` be a projective object of an abelian category `C`, placed in degree `n` of the derived
category. For every object `M` of `D(C)`, taking `n`-th cohomology is a bijection
`Hom_{D(C)}(P[-n], M) ≃ Hom_C(P, Hⁿ(M))`
(`DerivedCategory.homologyFunctor_map_bijective_of_projective`). No boundedness of `M` is needed:
`P` placed in one degree is K-projective, so every such morphism is a chain map, and a chain map
which vanishes on cohomology is null-homotopic since `P` is projective.

As a consequence, for a short exact sequence `0 → X₁ → X₂ → X₃ → 0` in `C` with `X₁` and `X₂`
projective, every morphism from `X₃` placed in degree zero to every shift of `M` vanishes if and
only if precomposition with `X₁ → X₂` is a bijection `Hom(X₂, Hⁿ(M)) → Hom(X₁, Hⁿ(M))` for every
`n` (`CategoryTheory.ShortComplex.ShortExact.forall_singleFunctor_hom_eq_zero_iff`). This is the
form in which the projective dimension of `X₃`, at most one, enters into derived completeness.

## Main results

* `DerivedCategory.homologyFunctor_map_bijective_of_projective`: for a projective `P`, `Hⁿ` is a
  bijection from morphisms `P[-n] ⟶ M` to morphisms `P ⟶ Hⁿ(M)`.
* `CategoryTheory.Pretriangulated.forall_hom_shift_eq_zero_iff`: in a pretriangulated category,
  the third object of a distinguished triangle `X₁ → X₂ → X₃ → X₁⟦1⟧` has no nonzero morphism to
  any shift of `M` if and only if precomposition with `X₁ → X₂` is bijective on morphisms to every
  shift of `M`.
* `CategoryTheory.ShortComplex.ShortExact.forall_singleFunctor_hom_eq_zero_iff`: the
  corresponding statement in `D(C)` for a projective presentation of length one, in terms of the
  cohomology of `M`.
-/

public section

open CategoryTheory Limits Pretriangulated

universe w v u

namespace CategoryTheory.Pretriangulated

variable {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The third object of a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` has no nonzero
morphism to any shift of `M` if and only if precomposition with `X₁ ⟶ X₂` is a bijection
`Hom(X₂, M⟦n⟧) → Hom(X₁, M⟦n⟧)` for every `n`. -/
theorem forall_hom_shift_eq_zero_iff {T : Triangle D} (hT : T ∈ distTriang D) (M : D) :
    (∀ (n : ℤ) (φ : T.obj₃ ⟶ M⟦n⟧), φ = 0) ↔
      ∀ n : ℤ, Function.Bijective fun g : T.obj₂ ⟶ M⟦n⟧ ↦ T.mor₁ ≫ g := by
  -- Shifting by `1` identifies morphisms `X ⟶ M⟦n⟧` with morphisms `X⟦1⟧ ⟶ M⟦n + 1⟧`.
  let e (n : ℤ) : (M⟦n⟧)⟦(1 : ℤ)⟧ ≅ M⟦n + 1⟧ := (shiftFunctorAdd' D n 1 (n + 1) rfl).symm.app M
  constructor
  · intro h n
    refine ⟨fun g₁ g₂ hg ↦ ?_, fun k ↦ ?_⟩
    · dsimp only at hg
      rw [← sub_eq_zero]
      obtain ⟨φ, hφ⟩ := Triangle.yoneda_exact₂ T hT (g₁ - g₂) (by rw [Preadditive.comp_sub, hg,
        sub_self])
      rw [hφ, h n φ, comp_zero]
    · -- `k` extends along `X₁ ⟶ X₂` since its composite with `X₃⟦-1⟧ ⟶ X₁` vanishes.
      have hrot := inv_rot_of_distTriang T hT
      have key (k' : T.invRotate.obj₂ ⟶ M⟦n⟧) : ∃ g, k' = T.invRotate.mor₂ ≫ g :=
        Triangle.yoneda_exact₂ _ hrot k' (by
          apply (shiftFunctor D (1 : ℤ)).map_injective
          rw [Functor.map_zero, ← cancel_mono (e n).hom, zero_comp]
          have h' := h (n + 1) (((shiftFunctorCompIsoId D (-1 : ℤ) 1 (by lia)).app T.obj₃).inv ≫
            (T.invRotate.mor₁ ≫ k')⟦1⟧' ≫ (e n).hom)
          exact (Iso.cancel_iso_inv_left _ _ _).1 (h'.trans comp_zero.symm))
      obtain ⟨g, hg⟩ := key k
      exact ⟨g, hg.symm⟩
  · intro h n φ
    -- The composite `X₂ ⟶ X₃ ⟶ M⟦n⟧` vanishes on `X₁`, so it is zero.
    have h₂ : T.mor₂ ≫ φ = 0 :=
      (h n).1 (by dsimp only; rw [comp_distTriang_mor_zero₁₂_assoc _ hT, comp_zero, zero_comp])
    obtain ⟨ψ, rfl⟩ := Triangle.yoneda_exact₃ T hT φ h₂
    -- `ψ : X₁⟦1⟧ ⟶ M⟦n⟧` extends along `X₁⟦1⟧ ⟶ X₂⟦1⟧`.
    let e' : M⟦n⟧ ≅ (M⟦n - 1⟧)⟦(1 : ℤ)⟧ := (shiftFunctorAdd' D (n - 1) 1 n (by lia)).app M
    obtain ⟨θ, hθ⟩ := (shiftFunctor D (1 : ℤ)).map_surjective (ψ ≫ e'.hom)
    obtain ⟨χ, rfl⟩ := (h (n - 1)).2 θ
    rw [← cancel_mono e'.hom, Category.assoc, ← hθ, Functor.map_comp,
      comp_distTriang_mor_zero₃₁_assoc _ hT, zero_comp, zero_comp]

end CategoryTheory.Pretriangulated

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

open HomologicalComplex

section Chain

variable {P : C} [Projective P] {L : CochainComplex C ℤ} {n : ℤ}

omit [HasDerivedCategory.{w} C] in
/-- A morphism from `P` to `Hⁿ(L)` is the cohomology of a chain map from `P` placed in degree
`n`, through a lift of it to the cycles. -/
private lemma exists_homologyMap_eq (α : P ⟶ L.homology n) :
    ∃ g : (CochainComplex.singleFunctor C n).obj P ⟶ L,
      homologyMap g n = (singleObjHomologySelfIso _ n P).hom ≫ α := by
  obtain ⟨β, hβ⟩ : ∃ β, β ≫ L.homologyπ n = α :=
    ⟨Projective.factorThru α (L.homologyπ n), Projective.factorThru_comp _ _⟩
  refine ⟨mkHomFromSingle (β ≫ L.iCycles n) (by rintro k rfl; simp), ?_⟩
  have hc : cyclesMap (mkHomFromSingle (β ≫ L.iCycles n) (by rintro k rfl; simp)) n =
      (singleObjCyclesSelfIso _ n P).hom ≫ β := by
    rw [← cancel_mono (L.iCycles n), cyclesMap_i, mkHomFromSingle_f, singleObjCyclesSelfIso_hom]
    simp
  rw [← cancel_epi (((single C _ n).obj P).homologyπ n), homologyπ_naturality, hc,
    homologyπ_singleObjHomologySelfIso_hom_assoc, Category.assoc, hβ]

/-- A chain map from `P` placed in degree `n` which vanishes on `Hⁿ` is null-homotopic, since
`P` is projective. -/
private lemma Q_map_eq_zero_of_homologyMap_eq_zero
    (g : (CochainComplex.singleFunctor C n).obj P ⟶ L) (hg : homologyMap g n = 0) :
    Q.map g = 0 := by
  let K := (CochainComplex.singleFunctor C n).obj P
  -- `g` is given by `γ : P ⟶ Zⁿ(L)`, whose image in `Hⁿ(L)` vanishes.
  let γ : P ⟶ L.cycles n :=
    L.liftCycles ((singleObjXSelf _ n P).inv ≫ g.f n) (n + 1) (by simp) (by simp)
  have hγ : γ ≫ L.homologyπ n = 0 := by
    have h := homologyπ_naturality g n
    rw [hg, comp_zero] at h
    have hc : cyclesMap g n = (singleObjCyclesSelfIso _ n P).hom ≫ γ := by
      rw [← cancel_mono (L.iCycles n), cyclesMap_i, singleObjCyclesSelfIso_hom]
      simp [γ]
    rw [hc, Category.assoc] at h
    rw [← cancel_epi (singleObjCyclesSelfIso _ n P).hom, comp_zero]
    exact h.symm
  -- So `γ` lifts along `Lⁿ⁻¹ ⟶ Zⁿ(L)`.
  have hex : (ShortComplex.mk (L.toCycles (n - 1) n) (L.homologyπ n)
      (L.toCycles_comp_homologyπ _ _)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (L.homologyIsCokernel (n - 1) n (by simp))
  let h : P ⟶ L.X (n - 1) := hex.liftFromProjective γ hγ
  have hh : h ≫ L.d (n - 1) n = (singleObjXSelf _ n P).inv ≫ g.f n := by
    have := hex.liftFromProjective_comp γ hγ
    dsimp at this
    rw [← L.toCycles_i, ← Category.assoc, this]
    simp [γ]
  -- The lift is a null-homotopy of `g`.
  let H : ∀ i j, (ComplexShape.up ℤ).Rel j i → (K.X i ⟶ L.X j) := fun i j hij ↦
    if hi : i = n then (singleObjXIsoOfEq _ n P i hi).hom ≫ h ≫ (L.XIsoOfEq (by
      simp only [ComplexShape.up_Rel] at hij; lia)).hom else 0
  have hgH : g = Homotopy.nullHomotopicMap' H := by
    refine from_single_hom_ext ?_
    rw [Homotopy.nullHomotopicMap'_f (c := ComplexShape.up ℤ) (k₂ := n - 1) (k₁ := n)
      (k₀ := n + 1) (by simp) (by simp)]
    have hd : K.d n (n + 1) = 0 :=
      (isZero_single_obj_X _ n P (n + 1) (by lia)).eq_of_tgt _ _
    rw [hd, zero_comp, zero_add]
    simp only [H, dite_true, XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id, Category.assoc, hh]
    simp [singleObjXSelf]
  rw [hgH, ← cancel_epi ((quotientCompQhIso C).hom.app K), ← quotientCompQhIso_hom_naturality,
    HomotopyCategory.eq_of_homotopy _ _ (Homotopy.nullHomotopy' H)]
  simp

private instance (P : C) [Projective P] (n i : ℤ) :
    Projective (((CochainComplex.singleFunctor C n).obj P).X i) := by
  by_cases hi : i = n
  · exact Projective.of_iso (singleObjXIsoOfEq _ n P i hi).symm inferInstance
  · exact (isZero_single_obj_X _ n P i hi).projective

omit [HasDerivedCategory.{w} C] in
/-- Postcomposition with an isomorphism is bijective. -/
private lemma bijective_comp_hom {D : Type*} [Category* D] (X : D) {Y Z : D} (i : Y ≅ Z) :
    Function.Bijective fun ψ : X ⟶ Y ↦ ψ ≫ i.hom :=
  ⟨fun a b hab ↦ by simpa using congr_arg (· ≫ i.inv) hab, fun c ↦ ⟨c ≫ i.inv, by simp⟩⟩

omit [HasDerivedCategory.{w} C] in
/-- Precomposition with an isomorphism is bijective. -/
private lemma bijective_hom_comp {D : Type*} [Category* D] {X Y : D} (i : X ≅ Y) (Z : D) :
    Function.Bijective fun ψ : Y ⟶ Z ↦ i.hom ≫ ψ :=
  ⟨fun a b hab ↦ by simpa using congr_arg (i.inv ≫ ·) hab, fun c ↦ ⟨i.inv ≫ c, by simp⟩⟩

end Chain

/-- **Morphisms from a projective object placed in one degree.** For a projective object `P` of
`C`, every object `M` of `D(C)` and every `n : ℤ`, taking `n`-th cohomology is a bijection from
morphisms `P[-n] ⟶ M` to morphisms `Hⁿ(P[-n]) ⟶ Hⁿ(M)`, and `Hⁿ(P[-n]) ≅ P`. -/
theorem homologyFunctor_map_bijective_of_projective (P : C) [Projective P]
    (M : DerivedCategory C) (n : ℤ) :
    Function.Bijective
      ((homologyFunctor C n).map : ((singleFunctor C n).obj P ⟶ M) → _) := by
  let H := homologyFunctor C n
  let K := (CochainComplex.singleFunctor C n).obj P
  have := CochainComplex.isKProjective_of_projective K n
  obtain ⟨L, ⟨e⟩⟩ : ∃ L, Nonempty (Q.obj L ≅ M) := ⟨_, ⟨Q.objObjPreimageIso M⟩⟩
  let η := homologyFunctorFactors C n
  -- The case of `Q.obj L`, by comparison with the cohomology of chain maps.
  have key : Function.Bijective (H.map : (Q.obj K ⟶ Q.obj L) → _) := by
    refine ⟨fun φ₁ φ₂ hφ ↦ ?_, fun ψ ↦ ?_⟩
    · rw [← sub_eq_zero]
      obtain ⟨g, hg⟩ := CochainComplex.IsKProjective.Q_map_surjective K L (φ₁ - φ₂)
      rw [← hg]
      refine Q_map_eq_zero_of_homologyMap_eq_zero g ?_
      have h := homologyFunctorFactors_hom_naturality g n
      rw [hg, H.map_sub, hφ, sub_self, zero_comp] at h
      exact (Iso.cancel_iso_hom_left ((homologyFunctorFactors C n).app K) _ _).1
        (h.symm.trans comp_zero.symm)
    · obtain ⟨g, hg⟩ := exists_homologyMap_eq (P := P) (L := L) (n := n)
        ((singleObjHomologySelfIso _ n P).inv ≫ η.inv.app K ≫ ψ ≫ η.hom.app L)
      refine ⟨Q.map g, ?_⟩
      have h := homologyFunctorFactors_hom_naturality g n
      rw [hg, Iso.hom_inv_id_assoc] at h
      rw [← cancel_mono (η.hom.app L), h]
      exact (homologyFunctorFactors C n).hom_inv_id_app_assoc _ _
  have h : (H.map : ((singleFunctor C n).obj P ⟶ M) → _) =
      (fun ψ ↦ ψ ≫ (H.mapIso e).hom) ∘ H.map ∘ fun φ ↦ φ ≫ e.symm.hom := by
    funext φ
    simp only [Function.comp_apply, Functor.mapIso_hom, Iso.symm_hom, ← H.map_comp,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h]
  exact ((bijective_comp_hom _ _).comp key).comp (bijective_comp_hom _ _)

end DerivedCategory

namespace CategoryTheory.ShortComplex.ShortExact

open DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- For a short exact sequence `0 → X₁ → X₂ → X₃ → 0` with `X₁` and `X₂` projective and an
object `M` of `D(C)`, every morphism from `X₃` placed in degree zero to every shift of `M`
vanishes if and only if precomposition with `X₁ → X₂` is a bijection
`Hom(X₂, H⁰(M⟦n⟧)) → Hom(X₁, H⁰(M⟦n⟧))` for every `n`. -/
theorem forall_singleFunctor_hom_eq_zero_iff {S : ShortComplex C} (hS : S.ShortExact)
    [Projective S.X₁] [Projective S.X₂] (M : DerivedCategory C) :
    (∀ (n : ℤ) (φ : (singleFunctor C 0).obj S.X₃ ⟶ M⟦n⟧), φ = 0) ↔
      ∀ n : ℤ, Function.Bijective
        fun g : S.X₂ ⟶ (DerivedCategory.homologyFunctor C 0).obj (M⟦n⟧) ↦ S.f ≫ g := by
  refine (forall_hom_shift_eq_zero_iff hS.singleTriangle_distinguished M).trans
    (forall_congr' fun n ↦ ?_)
  let H := DerivedCategory.homologyFunctor C 0
  let ε := singleFunctorCompHomologyFunctorIso C 0
  -- Under `H⁰`, precomposition with `X₁[0] ⟶ X₂[0]` is precomposition with `X₁ ⟶ X₂`.
  let Φ (X : C) : ((singleFunctor C 0).obj X ⟶ M⟦n⟧) → (X ⟶ H.obj (M⟦n⟧)) :=
    fun φ ↦ (ε.app X).symm.hom ≫ H.map φ
  have hΦ (X : C) [Projective X] : Function.Bijective (Φ X) :=
    (bijective_hom_comp (ε.app X).symm _).comp (homologyFunctor_map_bijective_of_projective X _ 0)
  have hcomm : Φ S.X₁ ∘ (fun g ↦ (singleFunctor C 0).map S.f ≫ g) =
      (fun g ↦ S.f ≫ g) ∘ Φ S.X₂ := by
    ext g
    simp only [Function.comp_apply, Φ, H.map_comp]
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    exact (ε.inv.naturality S.f).symm
  dsimp only [singleTriangle_obj₂, singleTriangle_mor₁]
  rw [← Function.Bijective.of_comp_iff' (hΦ S.X₁), hcomm,
    Function.Bijective.of_comp_iff _ (hΦ S.X₂)]

end CategoryTheory.ShortComplex.ShortExact
