/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Effective.CanonicalSection
public import TauCeti.AlgebraicGeometry.LineBundle.TwistedSections
public import TauCeti.AlgebraicGeometry.LineBundle.Monoidal
public import TauCeti.AlgebraicGeometry.VectorBundle.FixedRank
public import TauCeti.AlgebraicGeometry.Modules.SchemeTheoreticSupport
public import TauCeti.AlgebraicGeometry.Modules.FiniteType
public import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Basic
import TauCeti.AlgebraicGeometry.Modules.Sections
import TauCeti.AlgebraicGeometry.Modules.Stalk
import TauCeti.LinearAlgebra.Finsupp.LinearCombination

/-!
# Full-rank trivial subsheaves of twisted vector bundles on curves

Let `X` be an integral Noetherian scheme all of whose points have codimension at most one, for
instance a proper integral curve over a field, possibly singular, and let `E` be a vector bundle of
constant rank `r` on `X`. This file shows that after twisting by a suitable line bundle `L`, the
bundle `E ⊗ L` contains the trivial bundle `𝒪_X^r` with a quotient supported on finitely many
points (`FiniteLocallyFreeSheaf.FixedRank.exists_mono_free_twist_finite_support`).

Near the generic point, `E` has a local frame `t₁, …, t_r` over some open `V`
(`FiniteLocallyFreeSheaf.exists_bijective_linearCombination`). Choose an effective Cartier divisor
`D` whose canonical section `s` vanishes nowhere on an open `X_s ⊆ V` containing the generic point
(`Scheme.CartierDivisor.exists_isEffective_nonvanishingLocus_le`). For `n` large, every
`t_k ⊗ sⁿ` extends from `X_s` to a global section of `E ⊗ 𝒪_X(D)ⁿ` (Hartshorne, Lemma II.5.14),
and these global sections define a morphism `𝒪_X^r ⟶ E ⊗ 𝒪_X(D)ⁿ` which is an isomorphism over
`X_s`. It is therefore injective, as the sections of `𝒪_X^r` over a nonempty open are determined
by their restrictions to `X_s`, and its cokernel vanishes at the generic point, hence has finite
support on a scheme of dimension at most one.

Comparing a vector bundle with a trivial one by such a modification reduces statements about the
degree of vector bundles on curves to the trivial bundle, line bundles and finitely supported
sheaves, as for the degree of a tensor product,
`FiniteLocallyFreeSheaf.FixedRank.vectorBundleDegree_tensor_of_isCurveOver`.

## Main results

* `FiniteLocallyFreeSheaf.FixedRank.exists_mono_free_twist_finite_support`: some twist `E ⊗ L`
  contains `𝒪_X^r` with finitely supported quotient.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Lemma II.5.14.
* [The Stacks Project, Section 33.44, Degrees on curves](https://stacks.math.columbia.edu/tag/0AYQ),
  Lemma 0AYX, the degree of a tensor product of vector bundles, which this comparison serves.
-/

public section

open CategoryTheory Limits MonoidalCategory Opposite TopologicalSpace

namespace TauCeti

universe u

noncomputable section

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Let `t` be a local frame of `F` over `V`, `s` a global section of an invertible sheaf `L` whose
nonvanishing locus `X_s` lies in `V`, and `t'` global sections of `F ⊗ Lⁿ` restricting to
`t k ⊗ sⁿ` on `X_s`. Then the morphism `𝒪_X^ι ⟶ F ⊗ Lⁿ` defined by `t'` is bijective on sections
over every open contained in `X_s`. -/
private lemma bijective_app_freeHomEquiv_symm {F L : X.Modules}
    [SheafOfModules.isInvertible X L] {ι : Type u} [Fintype ι] {V : X.Opens} (s : Γ(L, ⊤))
    (j : L.nonvanishingLocus s ⟶ V) (t : ι → Γ(F, V))
    (ht : ∀ (W : X.Opens) (i : W ⟶ V),
      Function.Bijective (Fintype.linearCombination Γ(X, W) fun k ↦ F.presheaf.map i.op (t k)))
    {n : ℕ} (t' : ι → Γ(F ⊗ tensorPow L n, ⊤))
    (ht' : ∀ k, (F ⊗ tensorPow L n).presheaf.map (homOfLE (L.nonvanishingLocus_le s)).op (t' k) =
      F.tmulRight (Scheme.Modules.tensorPowSection
        (L.presheaf.map (homOfLE (L.nonvanishingLocus_le s)).op s) n) (F.presheaf.map j.op (t k)))
    (W : X.Opens) (hW : W ≤ L.nonvanishingLocus s) :
    Function.Bijective (Scheme.Modules.Hom.app ((F ⊗ tensorPow L n).freeHomEquiv.symm
      fun k ↦ (F ⊗ tensorPow L n).sectionsEquivTop.symm (t' k)) W) := by
  let i : W ⟶ L.nonvanishingLocus s := homOfLE hW
  let sW := L.presheaf.map (homOfLE le_top : W ⟶ ⊤).op s
  -- The image of the `k`-th basis section is `t k ⊗ sⁿ` over `W`.
  have himg (k : ι) : ((F ⊗ tensorPow L n).sectionsEquivTop.symm (t' k)).val (op W) =
      F.tmulRight (Scheme.Modules.tensorPowSection sW n) (F.presheaf.map (i ≫ j).op (t k)) := by
    rw [Scheme.Modules.sectionsEquivTop_symm_val,
      show W.leTop = i ≫ homOfLE (L.nonvanishingLocus_le s) from Subsingleton.elim _ _, op_comp,
      Functor.map_comp_apply, ht' k, Scheme.Modules.map_tmulRight_tensorPowSection]
    simp only [← Functor.map_comp_apply, ← op_comp]
    -- Both sides restrict `s` along a morphism `W ⟶ ⊤` of the thin category `X.Opens`, and any two
    -- such morphisms are equal.
    rfl
  let B := TauCeti.SheafOfModules.freeBasis (R := X.sheaf) ι (op W)
  -- Through the standard basis `B`, the morphism is `c ↦ (∑ c k • t k) ⊗ sⁿ`.
  have key (c : ι → Γ(X, W)) : Scheme.Modules.Hom.app ((F ⊗ tensorPow L n).freeHomEquiv.symm
      fun k ↦ (F ⊗ tensorPow L n).sectionsEquivTop.symm (t' k)) W (B.equivFun.symm c) =
      F.tmulRight (Scheme.Modules.tensorPowSection sW n)
        (Fintype.linearCombination Γ(X, W) (fun k ↦ F.presheaf.map (i ≫ j).op (t k)) c) := by
    rw [Module.Basis.equivFun_symm_apply]
    simp only [B, TauCeti.SheafOfModules.freeBasis_apply, Fintype.linearCombination_apply,
      map_sum, map_smul]
    refine (TauCeti.SheafOfModules.freeHomEquiv_symm_val_app_sum_smul (R := X.ringCatSheaf)
      (fun k ↦ (F ⊗ tensorPow L n).sectionsEquivTop.symm (t' k)) (op W) c).trans ?_
    -- `PresheafOfModules.sections.eval σ` is the abbreviation `σ.val`.
    exact Finset.sum_congr rfl fun k _ ↦ by rw [← himg k]; rfl
  -- Both factors are bijective: `t` is a frame over `W`, and `sⁿ` is a basis of `Lⁿ` there.
  have hcomp := (Scheme.Modules.bijective_tmulRight_tensorPowSection_of_le_nonvanishingLocus F sW
    (by rw [Scheme.Modules.nonvanishingLocus_map]; exact le_inf le_rfl hW) n).comp
    (ht W (i ≫ j))
  refine ⟨fun a b hab ↦ ?_, fun y ↦ ?_⟩
  · rw [← B.equivFun.symm_apply_apply a, ← B.equivFun.symm_apply_apply b] at hab ⊢
    rw [key, key] at hab
    rw [hcomp.1 hab]
  · obtain ⟨c, hc⟩ := hcomp.2 y
    exact ⟨B.equivFun.symm c, (key c).trans hc⟩

namespace FiniteLocallyFreeSheaf.FixedRank

variable [IsIntegral X] [IsNoetherian X] {r : ℕ}

/-- **Vector bundles on curves contain twisted trivial bundles of full rank.** Let `X` be an
integral Noetherian scheme all of whose points have codimension at most one, for instance a proper
integral curve over a field, possibly singular, and let `E` be a vector bundle of constant rank
`r`. Then for some line bundle `L` there is a monomorphism `𝒪_X^r ⟶ E ⊗ L` whose cokernel is
supported on finitely many points. Equivalently, `E` contains `(L⁻¹)^{⊕r}` with finitely supported
quotient. -/
theorem exists_mono_free_twist_finite_support (hX : ∀ x : X, Order.coheight x ≤ 1)
    (E : FixedRank X r) :
    ∃ (L : InvertibleSheaf X) (φ : (free X r).obj.obj ⟶ (E.twist L).obj.obj), Mono φ ∧
      {x : X | Nontrivial ((cokernel φ).presheaf.stalk x)}.Finite := by
  classical
  -- A frame `t` of `E` over a neighbourhood `V` of the generic point, indexed by `ULift (Fin r)`.
  obtain ⟨ι, _, hι, V, hηV, t, ht⟩ :=
    FiniteLocallyFreeSheaf.exists_bijective_linearCombination E.obj (genericPoint X)
  rw [rank_apply] at hι
  let e : ULift.{u} (Fin r) ≃ ι := Fintype.equivOfCardEq (by simp [hι])
  have ht₀ (W : X.Opens) (i : W ⟶ V) : Function.Bijective (Fintype.linearCombination Γ(X, W)
      fun k ↦ E.obj.obj.presheaf.map i.op (t (e k))) :=
    (Fintype.bijective_linearCombination_comp_equiv_iff e).mpr (ht W i)
  have : Nonempty V := ⟨⟨_, hηV⟩⟩
  -- An effective divisor `D` whose canonical section `s` vanishes nowhere on `X_s ⊆ V`, and an `n`
  -- such that every `t k ⊗ sⁿ` over `X_s` extends to a global section `t' k` of `E ⊗ 𝒪_X(D)ⁿ`.
  obtain ⟨D, hD, hDV⟩ := Scheme.CartierDivisor.exists_isEffective_nonvanishingLocus_le hX V
  obtain ⟨n, hn⟩ := (Filter.eventually_all.mpr fun k : ULift.{u} (Fin r) ↦
    Scheme.Modules.eventually_exists_map_eq_tmulRight_tensorPowSection E.obj.obj (U := ⊤)
      (by simpa using isCompact_univ) (by simpa using isQuasiSeparated_univ) hD.canonicalSection
      (E.obj.obj.presheaf.map (homOfLE hDV).op (t (e k)))).exists
  choose t' ht' using hn
  let L : InvertibleSheaf X := ⟨tensorPow D.sheaf n, inferInstance⟩
  have h₁ : (free X r).obj.obj =
      _root_.SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)) := by
    rw [free_obj, FiniteLocallyFreeSheaf.free_obj]
  -- The morphism `𝒪_X^r ⟶ E ⊗ 𝒪_X(D)ⁿ` sending the standard basis to the sections `t' k`.
  let φ : (free X r).obj.obj ⟶ (E.twist L).obj.obj := eqToHom h₁ ≫
    (E.obj.obj ⊗ tensorPow D.sheaf n).freeHomEquiv.symm
      (fun k ↦ (E.obj.obj ⊗ tensorPow D.sheaf n).sectionsEquivTop.symm (t' k)) ≫
    eqToHom (twist_obj_obj E L).symm
  have hφ (W : X.Opens) (hW : W ≤ D.sheaf.nonvanishingLocus hD.canonicalSection) :
      Function.Bijective (Scheme.Modules.Hom.app φ W) := by
    -- The two `eqToHom` factors are isomorphisms, hence bijective on sections.
    have hiso {A B : X.Modules} (h : A = B) : Function.Bijective ((eqToHom h).app W) :=
      ConcreteCategory.bijective_of_isIso _
    have := (hiso (twist_obj_obj E L).symm).comp
      ((bijective_app_freeHomEquiv_symm _ (homOfLE hDV) _ ht₀ t' ht' W hW).comp (hiso h₁))
    rw [← ConcreteCategory.coe_comp, ← ConcreteCategory.coe_comp] at this
    -- `Scheme.Modules.Hom.comp_app` holds by `rfl`, so `φ.app W` is definitionally the composite
    -- of the maps on sections of the three factors of `φ`.
    exact this
  have hη := hD.genericPoint_mem_nonvanishingLocus
  refine ⟨L, φ, φ.mono_of_injective_app_of_genericPoint_mem hη
    (fun W hW ↦ (hφ W hW).1) fun W W' i hW' ↦ ?_, ?_⟩
  · -- The restriction maps of `𝒪_X^r` to nonempty opens are injective.
    have : Nonempty W' := ⟨⟨_, hW'⟩⟩
    rw [h₁]
    exact TauCeti.SheafOfModules.free_map_injective (R := X.sheaf) i.op
      (map_injective_of_isIntegral X i)
  · -- The cokernel is coherent and vanishes at the generic point, so it has finite support.
    have : (cokernel φ).IsQuasicoherent := Scheme.Modules.isQuasicoherent_cokernel φ
    have : (cokernel φ).IsFiniteType := Scheme.Modules.isFiniteType_of_epi (cokernel.π φ)
    have hdim : topologicalKrullDim X ≤ 1 :=
      TauCeti.topologicalKrullDim_le_of_forall_coheight_le hX
    exact Scheme.Modules.finite_setOf_nontrivial_stalk_of_subsingleton_stalk_genericPoint
      (cokernel φ) (fun A ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ A.val A.property) hdim
      (φ.subsingleton_stalk_cokernel_of_surjective_app hη fun W hW ↦ (hφ W hW).2)

end FiniteLocallyFreeSheaf.FixedRank

end AlgebraicGeometry

end

end TauCeti
