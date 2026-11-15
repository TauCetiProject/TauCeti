/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.PeriodicResolution
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Resolution
public import TauCeti.Algebra.Homology.ModuleCat.Minimal
import TauCeti.RingTheory.CohenMacaulay.Maximal.Hypersurface
import TauCeti.RingTheory.LocalRing.Module

/-!
# Minimal matrix factorizations and projective summands of cokernels

A finite-projective matrix factorization `X = (X₀ --d₀--> X₁ --d₁--> X₀)` of `w : S` is *minimal*
(`TauCeti.MatrixFactorization.IsMinimal`) if both differentials take values in the Jacobson radical
of `S` times their target; over a local ring `(S, 𝔪)` this means that in any bases of the finite
free modules `X₀` and `X₁`, all matrix entries of `d₀` and `d₁` lie in `𝔪` (Eisenbud, Section 5).

When `(S, 𝔪)` is local and `R = S ⧸ (w)` is local (so `w ∈ 𝔪`), reducing modulo `w` preserves and
reflects minimality: `X` is minimal if and only if the reduced two-periodic complex
`quotientPeriodicComplex.obj X` is minimal, and (when `w` is a non-zero-divisor) if and only if the
periodic projective resolution `quotientCokernelProjectiveResolution hw X` is minimal.

Eisenbud's key observation in Section 5 is that for a minimal length-one `S`-projective resolution
`0 → P --f--> Q --g--> M → 0` (`range f ≤ 𝔪 • Q`) of an `R`-module `M`, the induced matrix
factorization `ofInjective f` is minimal — i.e., its odd-to-even differential `d₁` also satisfies
`range d₁ ≤ 𝔪 • P` — if and only if `M` has no nonzero projective `R`-retract
(`TauCeti.MatrixFactorization.range_d₁_le_maximalIdeal_smul_iff_forall_projective_retract_isZero`,
`TauCeti.MatrixFactorization.isMinimal_ofInjective_iff`). Geometrically, splitting off trivial
rank-one factorizations `S --1--> S --w--> S` on the matrix-factorization side corresponds to
splitting off free summands `R` on the cokernel side.

## Main definitions

* `TauCeti.MatrixFactorization.IsMinimal`: both differentials of a matrix factorization have image
  in `Ring.jacobson S • ⊤`.

## Main results

* `TauCeti.MatrixFactorization.quotientPeriodicComplex_obj_isMinimal_iff` and
  `TauCeti.MatrixFactorization.resolutionComplex_quotientPeriodicComplex_isMinimal_iff`: over a
  local ring `S` with local quotient `S ⧸ (w)`, minimality of `X` agrees with minimality of its
  reduced two-periodic complex and of its unfolded resolution complexes.
* `TauCeti.MatrixFactorization.range_d₁_le_maximalIdeal_smul_iff_forall_projective_retract_isZero`:
  for a non-zero-divisor `w`, `range d₁ ≤ 𝔪 • X₀` holds if and only if every projective
  `S ⧸ (w)`-retract of the reduced cokernel is zero.
* `TauCeti.MatrixFactorization.isMinimal_ofInjective_iff`: for a minimal length-one `S`-projective
  resolution of `M`, `ofInjective` is minimal if and only if `M` has no nonzero projective
  `S ⧸ (w)`-retract.

## References

* David Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Section 5 and Section 6.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits IsLocalRing
open scoped TensorProduct ChangeOfRings

section QuotientMinimal

variable {S : Type u} [CommRing S] [IsLocalRing S] {w : S} [IsLocalRing (S ⧸ Ideal.span {w})]

/-- Over a local ring `S` with local quotient `R = S ⧸ (w)`, a pure tensor `1 ⊗ m` in `R ⊗[S] M`
lies in `𝔪_R • (R ⊗[S] M)` if and only if `m` lies in `𝔪_S • M`. -/
theorem TensorProduct.one_tmul_mem_maximalIdeal_smul_top_iff {M : Type*} [AddCommGroup M]
    [Module S M] (m : M) :
    (1 : S ⧸ Ideal.span {w}) ⊗ₜ[S] m ∈
        (maximalIdeal (S ⧸ Ideal.span {w}) • ⊤ :
          Submodule (S ⧸ Ideal.span {w}) ((S ⧸ Ideal.span {w}) ⊗[S] M)) ↔
      m ∈ (maximalIdeal S • ⊤ : Submodule S M) := by
  have hloc : IsLocalHom (Ideal.Quotient.mk (Ideal.span {w})) :=
    .of_surjective _ Ideal.Quotient.mk_surjective
  have hmax : (maximalIdeal S).map (Ideal.Quotient.mk (Ideal.span {w})) =
      maximalIdeal (S ⧸ Ideal.span {w}) :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hwm : w ∈ maximalIdeal S :=
    TauCeti.IsLocalRing.mem_maximalIdeal_of_isLocalRing_quotient_span_singleton
  constructor
  · intro hm
    -- Every element of `𝔪_R • (R ⊗[S] M)` has the form `1 ⊗ z` with `z ∈ 𝔪_S • M`.
    have hex : ∃ z ∈ (maximalIdeal S • ⊤ : Submodule S M),
        (1 : S ⧸ Ideal.span {w}) ⊗ₜ[S] z = (1 : S ⧸ Ideal.span {w}) ⊗ₜ[S] m := by
      refine Submodule.smul_induction_on hm (fun r hr t _ ↦ ?_)
        (fun _ _ ⟨z₁, hz₁, h₁⟩ ⟨z₂, hz₂, h₂⟩ ↦
          ⟨z₁ + z₂, add_mem hz₁ hz₂, by rw [TensorProduct.tmul_add, h₁, h₂]⟩)
      obtain ⟨s, hs, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1
        (hmax.symm ▸ hr)
      obtain ⟨x, rfl⟩ := TensorProduct.exists_one_tmul_eq (Ideal.span {w}) t
      refine ⟨s • x, Submodule.smul_mem_smul hs Submodule.mem_top, ?_⟩
      exact (TensorProduct.smul_tmul s (1 : S ⧸ Ideal.span {w}) x).symm
    obtain ⟨z, hz, heq⟩ := hex
    have hzero : (1 : S ⧸ Ideal.span {w}) ⊗ₜ[S] (m - z) = 0 := by
      rw [TensorProduct.tmul_sub, sub_eq_zero]
      exact heq.symm
    obtain ⟨y, hy⟩ := (TensorProduct.one_tmul_eq_zero_iff_exists_smul_eq w (m - z)).1 hzero
    have hmz : m - z ∈ (maximalIdeal S • ⊤ : Submodule S M) :=
      hy ▸ Submodule.smul_mem_smul hwm Submodule.mem_top
    simpa only [add_sub_cancel] using add_mem hz hmz
  · intro hm
    refine Submodule.smul_induction_on hm (fun s hs x _ ↦ ?_) (fun x y hx hy ↦ ?_)
    · have hsmul : (1 : S ⧸ Ideal.span {w}) ⊗ₜ[S] (s • x) =
          Ideal.Quotient.mk (Ideal.span {w}) s • ((1 : S ⧸ Ideal.span {w}) ⊗ₜ[S] x) :=
        (TensorProduct.smul_tmul s (1 : S ⧸ Ideal.span {w}) x).symm.trans
          (TensorProduct.smul_tmul' (Ideal.Quotient.mk (Ideal.span {w}) s)
            (1 : S ⧸ Ideal.span {w}) x).symm
      rw [hsmul]
      exact Submodule.smul_mem_smul
        (map_nonunit (Ideal.Quotient.mk (Ideal.span {w})) s hs) Submodule.mem_top
    · rw [TensorProduct.tmul_add]
      exact add_mem hx hy

/-- Extending scalars along `S → S ⧸ (w)` preserves and reflects the maximal-ideal range condition
on module morphisms. -/
theorem ModuleCat.range_extendScalars_quotient_le_maximalIdeal_smul_iff
    {P Q : ModuleCat.{u} S} (g : P ⟶ Q) :
    LinearMap.range
        (((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {w}))).map g).hom) ≤
      maximalIdeal (S ⧸ Ideal.span {w}) • ⊤ ↔
      LinearMap.range g.hom ≤ maximalIdeal S • ⊤ := by
  constructor
  · rintro hg _ ⟨x, rfl⟩
    refine (TensorProduct.one_tmul_mem_maximalIdeal_smul_top_iff (w := w) (g.hom x)).1 ?_
    refine hg ⟨(1 : S ⧸ Ideal.span {w}) ⊗ₜ[S, Ideal.Quotient.mk (Ideal.span {w})] x, ?_⟩
    exact ModuleCat.ExtendScalars.map_tmul (Ideal.Quotient.mk (Ideal.span {w})) g 1 x
  · rintro hg _ ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := TensorProduct.exists_one_tmul_eq (M := P) (Ideal.span {w}) z
    change ((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {w}))).map g)
        ((1 : S ⧸ Ideal.span {w}) ⊗ₜ[S, Ideal.Quotient.mk (Ideal.span {w})] x) ∈ _
    rw [ModuleCat.ExtendScalars.map_tmul]
    exact (TensorProduct.one_tmul_mem_maximalIdeal_smul_top_iff (w := w) (g.hom x)).2
      (hg ⟨x, rfl⟩)

end QuotientMinimal

namespace TauCeti.MatrixFactorization

variable {S : Type u} [CommRing S] {w : S}

/-! ### Minimal matrix factorizations -/

/-- A matrix factorization `X = (X₀ --d₀--> X₁ --d₁--> X₀)` over a commutative ring `S` is
*minimal* if both differentials have image contained in the Jacobson radical times their target. -/
def IsMinimal (X : MatrixFactorization S w) : Prop :=
  LinearMap.range X.obj.d₀.hom.hom ≤ Ring.jacobson S • ⊤ ∧
    LinearMap.range X.obj.d₁.hom.hom ≤ Ring.jacobson S • ⊤

/-- Unfolds `TauCeti.MatrixFactorization.IsMinimal`. -/
theorem isMinimal_iff (X : MatrixFactorization S w) :
    X.IsMinimal ↔
      LinearMap.range X.obj.d₀.hom.hom ≤ Ring.jacobson S • ⊤ ∧
        LinearMap.range X.obj.d₁.hom.hom ≤ Ring.jacobson S • ⊤ :=
  Iff.rfl

/-- Over a local ring, minimality means both differentials map into `maximalIdeal S • ⊤`. -/
theorem isMinimal_iff_range_le_maximalIdeal_smul [IsLocalRing S] (X : MatrixFactorization S w) :
    X.IsMinimal ↔
      LinearMap.range X.obj.d₀.hom.hom ≤ maximalIdeal S • ⊤ ∧
        LinearMap.range X.obj.d₁.hom.hom ≤ maximalIdeal S • ⊤ := by
  rw [isMinimal_iff, ringJacobson_eq_maximalIdeal]

/-- Minimality is preserved along isomorphisms of matrix factorizations. -/
theorem IsMinimal.of_iso {X Y : MatrixFactorization S w} (hX : X.IsMinimal) (e : X ≅ Y) :
    Y.IsMinimal := by
  have hf₀ : e.inv.hom.f₀.hom ≫ e.hom.hom.f₀.hom = 𝟙 Y.obj.X₀.obj :=
    congrArg (fun k : Y ⟶ Y ↦ k.hom.f₀.hom) e.inv_hom_id
  have hf₁ : e.inv.hom.f₁.hom ≫ e.hom.hom.f₁.hom = 𝟙 Y.obj.X₁.obj :=
    congrArg (fun k : Y ⟶ Y ↦ k.hom.f₁.hom) e.inv_hom_id
  have comm₀ : e.inv.hom.f₀.hom ≫ X.obj.d₀.hom ≫ e.hom.hom.f₁.hom = Y.obj.d₀.hom := by
    have h := congrArg (fun m ↦ m.hom ≫ e.hom.hom.f₁.hom) e.inv.hom.comm₀
    simpa [Category.assoc, hf₁] using h
  have comm₁ : e.inv.hom.f₁.hom ≫ X.obj.d₁.hom ≫ e.hom.hom.f₀.hom = Y.obj.d₁.hom := by
    have h := congrArg (fun m ↦ m.hom ≫ e.hom.hom.f₀.hom) e.inv.hom.comm₁
    simpa [Category.assoc, hf₀] using h
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [← comm₀]
    exact Submodule.smul_top_le_comap_smul_top (Ring.jacobson S) e.hom.hom.f₁.hom.hom
      (hX.1 ⟨e.inv.hom.f₀.hom.hom x, rfl⟩)
  · rintro _ ⟨y, rfl⟩
    rw [← comm₁]
    exact Submodule.smul_top_le_comap_smul_top (Ring.jacobson S) e.hom.hom.f₀.hom.hom
      (hX.2 ⟨e.inv.hom.f₁.hom.hom y, rfl⟩)

/-- Isomorphic matrix factorizations are simultaneously minimal. -/
theorem isMinimal_of_iso_iff {X Y : MatrixFactorization S w} (e : X ≅ Y) :
    X.IsMinimal ↔ Y.IsMinimal :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

/-- Parity shift preserves and reflects minimality. -/
@[simp]
theorem isMinimal_parityShift_iff (X : MatrixFactorization S w) :
    (parityShift.obj X).IsMinimal ↔ X.IsMinimal := by
  have hd₀ : (-X.obj.d₁).hom.hom = -X.obj.d₁.hom.hom := rfl
  have hd₁ : (-X.obj.d₀).hom.hom = -X.obj.d₀.hom.hom := rfl
  rw [isMinimal_iff, isMinimal_iff, parityShift_obj_d₀, parityShift_obj_d₁, hd₀, hd₁,
    LinearMap.range_neg, LinearMap.range_neg, and_comm]

/-! ### Minimality of the reduced periodic complex and resolution -/

section LocalReduction

variable [IsLocalRing S] [IsLocalRing (S ⧸ Ideal.span {w})]

/-- Over a local ring `S` with local quotient `S ⧸ (w)`, the reduced two-periodic complex of `X`
is minimal if and only if `X` is minimal. -/
theorem quotientPeriodicComplex_obj_isMinimal_iff (X : MatrixFactorization S w) :
    (quotientPeriodicComplex.obj X).IsMinimal ↔ X.IsMinimal := by
  rw [HomologicalComplex.isMinimal_iff_forall_rel, isMinimal_iff_range_le_maximalIdeal_smul,
    ringJacobson_eq_maximalIdeal]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact (ModuleCat.range_extendScalars_quotient_le_maximalIdeal_smul_iff X.obj.d₀.hom).1
        (h 0 1 (zero_add 1))
    · exact (ModuleCat.range_extendScalars_quotient_le_maximalIdeal_smul_iff X.obj.d₁.hom).1
        (h 1 0 (by decide))
  · rintro ⟨hd₀, hd₁⟩ i j hij
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) i with rfl | rfl
    · obtain rfl : j = 1 := hij.symm.trans (zero_add 1)
      exact (ModuleCat.range_extendScalars_quotient_le_maximalIdeal_smul_iff X.obj.d₀.hom).2 hd₀
    · obtain rfl : j = 0 := hij.symm.trans (by decide)
      exact (ModuleCat.range_extendScalars_quotient_le_maximalIdeal_smul_iff X.obj.d₁.hom).2 hd₁

/-- Unfolding the reduced two-periodic complex of `X` from any starting parity `j : ℤ` gives a
minimal chain complex over `S ⧸ (w)` if and only if `X` is minimal. -/
theorem resolutionComplex_quotientPeriodicComplex_isMinimal_iff (X : MatrixFactorization S w)
    (j : ℤ) :
    (PeriodicComplex.resolutionComplex (quotientPeriodicComplex.obj X) j).IsMinimal ↔
      X.IsMinimal := by
  let Q := quotientPeriodicComplex.obj X
  rw [← quotientPeriodicComplex_obj_isMinimal_iff, ChainComplex.isMinimal_iff_range_d_succ_le,
    HomologicalComplex.isMinimal_iff_forall_rel]
  constructor
  · intro h a b hab
    -- Choose `k ∈ {0, 1}` so that `(j - k : ZMod 2) = b`, hence `(j - (k + 1) : ZMod 2) = a`.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ((j - k : ℤ) : ZMod 2) = b := by
      rcases (by decide : ∀ x y : ZMod 2, x = y ∨ x = y - 1) b (j : ZMod 2) with rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by push_cast; ring⟩
    have hk' : ((j - (k + 1 : ℕ) : ℤ) : ZMod 2) = a := by
      have hstep : ((j - (k + 1 : ℕ) : ℤ) : ZMod 2) + 1 = ((j - k : ℤ) : ZMod 2) := by
        push_cast; ring
      exact add_right_cancel (hstep.trans (hk.trans hab.symm))
    subst hk hk'
    rintro _ ⟨x, rfl⟩
    rw [← PeriodicComplex.resolutionComplex_d Q j k]
    exact h k ⟨x, rfl⟩
  · intro h k
    rw [PeriodicComplex.resolutionComplex_d]
    exact h _ _ (show ((j - (k + 1 : ℕ) : ℤ) : ZMod 2) + 1 = ((j - k : ℤ) : ZMod 2) by
      push_cast; ring)

/-- For a non-zero-divisor `w`, the periodic projective resolution of the reduced cokernel of `X`
is minimal if and only if `X` is minimal. -/
theorem quotientCokernelProjectiveResolution_complex_isMinimal_iff (hw : w ∈ nonZeroDivisors S)
    (X : MatrixFactorization S w) :
    (quotientCokernelProjectiveResolution hw X).complex.IsMinimal ↔ X.IsMinimal := by
  rw [quotientCokernelProjectiveResolution_complex]
  exact resolutionComplex_quotientPeriodicComplex_isMinimal_iff X 1

end LocalReduction

/-! ### Eisenbud's projective-retract criterion for minimality -/

section ProjectiveRetract

variable [IsLocalRing S] [IsLocalRing (S ⧸ Ideal.span {w})]

omit [IsLocalRing S] in
/-- Any nontrivial projective `S ⧸ (w)`-retract of a finite `S ⧸ (w)`-module `M` contains `S ⧸ (w)`
as a retract, hence yields a retract `S ⧸ (w)` of `M`. -/
private theorem nonempty_retract_self_of_nontrivial_projective_retract
    {M P : ModuleCat.{u} (S ⧸ Ideal.span {w})} [Module.Finite (S ⧸ Ideal.span {w}) M]
    [Projective P] [Nontrivial P] (ret : Retract P M) :
    Nonempty (Retract (ModuleCat.of (S ⧸ Ideal.span {w}) (S ⧸ Ideal.span {w})) M) := by
  have hr_surj : Function.Surjective ret.r.hom :=
    Function.LeftInverse.surjective (fun p ↦ ConcreteCategory.congr_hom ret.retract p)
  have : Module.Finite (S ⧸ Ideal.span {w}) P := Module.Finite.of_surjective ret.r.hom hr_surj
  have : Module.Projective (S ⧸ Ideal.span {w}) P :=
    (IsProjective.iff_projective P).2 inferInstance
  have : Module.Free (S ⧸ Ideal.span {w}) P := Module.free_of_projective_of_isLocalRing
  let b := Module.Free.chooseBasis (S ⧸ Ideal.span {w}) P
  have : Nonempty (Module.Free.ChooseBasisIndex (S ⧸ Ideal.span {w}) P) := by
    by_contra! hemp
    exact not_subsingleton P b.repr.subsingleton
  obtain ⟨i₀⟩ := this
  let _ := Classical.decEq (Module.Free.ChooseBasisIndex (S ⧸ Ideal.span {w}) P)
  let retP : Retract (ModuleCat.of (S ⧸ Ideal.span {w}) (S ⧸ Ideal.span {w})) P :=
    { i := ModuleCat.ofHom (LinearMap.toSpanSingleton (S ⧸ Ideal.span {w}) P (b i₀))
      r := ModuleCat.ofHom (b.coord i₀)
      retract := ModuleCat.hom_ext <| LinearMap.ext fun r ↦ by
        change b.coord i₀ (r • b i₀) = r
        rw [map_smul, b.coord_apply, b.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one] }
  exact ⟨retP.trans ret⟩

/-- If `range d₁ ≤ 𝔪_S • X₀`, then `S ⧸ (w)` cannot be a retract of the reduced cokernel of `X`:
any such retract lifts to a functional `β : X₁ → S` with `β y ∉ 𝔪_S` and `β ∘ d₀` divisible by
`w`, contradicting `w * β y = β (d₀ (d₁ y)) ∈ w • 𝔪_S`. -/
private theorem not_nonempty_retract_self_of_range_d₁_le (hw : w ∈ nonZeroDivisors S)
    {X : MatrixFactorization S w} (hd₁ : LinearMap.range X.obj.d₁.hom.hom ≤ maximalIdeal S • ⊤)
    (retR : Retract (ModuleCat.of (S ⧸ Ideal.span {w}) (S ⧸ Ideal.span {w}))
      (cokernelFunctor.obj
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj) :
    False := by
  obtain ⟨y, hy⟩ := quotientCokernelπ_surjective X (retR.i.hom 1)
  have hπy : retR.r.hom (quotientCokernelπ X y) = 1 := by
    rw [hy]
    exact ConcreteCategory.congr_hom retR.retract 1
  -- Lift the `S`-linear composite `X₁ → M → S ⧸ (w)` across `S ↠ S ⧸ (w)`.
  have : Module.Projective S X.obj.X₁ := X.property.2
  let φ : X.obj.X₁ →ₗ[S] S ⧸ Ideal.span {w} :=
    (quotientCokernelπ X ≫
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).map retR.r).hom
  obtain ⟨β, hβ⟩ := Module.projective_lifting_property (Ideal.span {w}).mkQ φ
    (Submodule.mkQ_surjective _)
  have hβ_eq (z : X.obj.X₁) : Ideal.Quotient.mk (Ideal.span {w}) (β z) = φ z := congr($hβ z)
  have hβy : β y ∉ maximalIdeal S := fun hm ↦ by
    have hloc : IsLocalHom (Ideal.Quotient.mk (Ideal.span {w})) :=
      .of_surjective _ Ideal.Quotient.mk_surjective
    have h1 : (1 : S ⧸ Ideal.span {w}) ∈ maximalIdeal (S ⧸ Ideal.span {w}) := by
      have hφy : φ y = 1 := hπy
      rw [← hφy, ← hβ_eq y]
      exact map_nonunit _ (β y) hm
    exact (maximalIdeal.isMaximal (S ⧸ Ideal.span {w})).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hd₀_div (x : X.obj.X₀) : ∃ c : S, β (X.obj.d₀.hom.hom x) = w * c := by
    refine Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 ?_)
    have hφ0 : φ (X.obj.d₀.hom.hom x) = 0 := by
      change ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).map retR.r).hom
        ((quotientCokernelπ X).hom (X.obj.d₀.hom.hom x)) = 0
      rw [(exact_d₀_quotientCokernelπ X _).2 ⟨x, rfl⟩, map_zero]
    rw [hβ_eq, hφ0]
  have hsmul_div : ∀ x ∈ (maximalIdeal S • ⊤ : Submodule S X.obj.X₀),
      ∃ m ∈ maximalIdeal S, β (X.obj.d₀.hom.hom x) = w * m := fun x hx ↦
    Submodule.smul_induction_on hx
      (fun a ha x₀ _ ↦ by
        obtain ⟨c, hc⟩ := hd₀_div x₀
        exact ⟨a * c, Ideal.mul_mem_right c _ ha, by
          rw [map_smul, map_smul, smul_eq_mul, hc]; ring⟩)
      (fun x₁ x₂ ⟨m₁, hm₁, h₁⟩ ⟨m₂, hm₂, h₂⟩ ↦
        ⟨m₁ + m₂, add_mem hm₁ hm₂, by rw [map_add, map_add, h₁, h₂, mul_add]⟩)
  obtain ⟨m, hm, hwm_eq⟩ := hsmul_div (X.obj.d₁.hom.hom y) (hd₁ ⟨y, rfl⟩)
  have hwy : w * β y = w * m := by
    calc w * β y = β (w • y) := (β.map_smul w y).symm
      _ = β (X.obj.d₀.hom.hom (X.obj.d₁.hom.hom y)) := by rw [d₁_comp_d₀_apply]
      _ = w * m := hwm_eq
  exact hβy ((Module.Flat.isSMulRegular_of_nonZeroDivisors hw hwy) ▸ hm)

/-- If `range d₁ ≤ 𝔪_S • X₀`, then every projective `S ⧸ (w)`-retract of the reduced cokernel of
`X` is zero. -/
private theorem isZero_projective_retract_of_range_d₁_le (hw : w ∈ nonZeroDivisors S)
    {X : MatrixFactorization S w} (hd₁ : LinearMap.range X.obj.d₁.hom.hom ≤ maximalIdeal S • ⊤)
    (P : ModuleCat.{u} (S ⧸ Ideal.span {w})) [Projective P]
    (ret : Retract P
      (cokernelFunctor.obj
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj) :
    IsZero P := by
  cases subsingleton_or_nontrivial P
  · exact ModuleCat.isZero_of_subsingleton P
  · obtain ⟨retR⟩ := nonempty_retract_self_of_nontrivial_projective_retract ret
    exact False.elim (not_nonempty_retract_self_of_range_d₁_le hw hd₁ retR)

omit [IsLocalRing (S ⧸ Ideal.span {w})] in
/-- Any element `x ∉ 𝔪_S • P` of a projective module `P` over a local ring `S` admits an `S`-linear
functional `α : P →ₗ[S] S` with `α x = 1`. -/
private theorem exists_linearMap_eq_one_of_not_mem_maximalIdeal_smul {P : Type u} [AddCommGroup P]
    [Module S P] [Module.Projective S P] {x : P} (hx : x ∉ (maximalIdeal S • ⊤ : Submodule S P)) :
    ∃ α : P →ₗ[S] S, α x = 1 := by
  obtain ⟨φ₀, hφ₀⟩ := TauCeti.IsLocalRing.exists_linearMap_quotient_eq_one hx
  obtain ⟨α₀, hα₀⟩ := Module.projective_lifting_property (maximalIdeal S).mkQ φ₀
    (Submodule.mkQ_surjective _)
  have hu : IsUnit (α₀ x) := by
    rw [← notMem_maximalIdeal]
    intro hm
    have h01 : (0 : S ⧸ maximalIdeal S) = 1 := by
      rw [← (Submodule.Quotient.mk_eq_zero _).2 hm, ← Submodule.mkQ_apply,
        ← LinearMap.comp_apply, hα₀, hφ₀]
    exact zero_ne_one h01
  exact ⟨((hu.unit⁻¹ : Sˣ) : S) • α₀, hu.val_inv_mul⟩

omit [IsLocalRing (S ⧸ Ideal.span {w})] in
/-- Conversely, if `d₁ y ∉ 𝔪_S • X₀`, lifting a residue-field dual of `d₁ y` to `α : X₀ → S` with
`α (d₁ y) = 1` and composing `cokernelDesc` with the scalar-extension transpose of `α` modulo `w`
produces a retraction `M → S ⧸ (w)`. -/
private theorem nonempty_retract_self_of_not_range_d₁_le
    {X : MatrixFactorization S w} (hnot : ¬ LinearMap.range X.obj.d₁.hom.hom ≤ maximalIdeal S • ⊤) :
    Nonempty (Retract (ModuleCat.of (S ⧸ Ideal.span {w}) (S ⧸ Ideal.span {w}))
      (cokernelFunctor.obj
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj) := by
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := Set.not_subset.1 hnot
  have : Module.Projective S X.obj.X₀ := X.property.1
  obtain ⟨α, hαy⟩ := exists_linearMap_eq_one_of_not_mem_maximalIdeal_smul hy
  let R_mod := ModuleCat.of (S ⧸ Ideal.span {w}) (S ⧸ Ideal.span {w})
  let g : X.obj.X₀.obj ⟶
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj R_mod :=
    ModuleCat.ofHom (X := X.obj.X₀.obj)
      (Y := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj R_mod)
      ((Ideal.span {w}).mkQ ∘ₗ α)
  let r_hom :
      (cokernelFunctor.obj
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj ⟶ R_mod :=
    (cokernelDesc (Ideal.Quotient.mk_singleton_self w)
      ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).hom ≫
      ((ModuleCat.extendRestrictScalarsAdj.{u}
        (Ideal.Quotient.mk (Ideal.span {w}))).homEquiv _ _).symm g
  let m₀ : (cokernelFunctor.obj
      ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj :=
    quotientCokernelπ X y
  have hr_apply : r_hom.hom m₀ = 1 := by
    have hcomp : cokernelπ ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X) ≫
        r_hom =
        ((ModuleCat.extendRestrictScalarsAdj.{u}
          (Ideal.Quotient.mk (Ideal.span {w}))).homEquiv _ _).symm (X.obj.d₁.hom ≫ g) :=
      (cokernelπ_cokernelDesc_hom_assoc (Ideal.Quotient.mk_singleton_self w)
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X) _).trans
        (Adjunction.homEquiv_naturality_left_symm
          (ModuleCat.extendRestrictScalarsAdj.{u} (Ideal.Quotient.mk (Ideal.span {w})))
          X.obj.d₁.hom g).symm
    refine (congrArg r_hom.hom (quotientCokernelπ_apply X y)).trans ?_
    refine (ConcreteCategory.congr_hom hcomp _).trans ?_
    refine (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply (M := X.obj.X₁.obj) _ y).symm.trans ?_
    rw [Equiv.apply_symm_apply]
    change Ideal.Quotient.mk (Ideal.span {w}) (α (X.obj.d₁.hom.hom y)) = 1
    rw [hαy, map_one]
  refine ⟨{ i := ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ m₀)
            r := r_hom
            retract := ModuleCat.hom_ext <| LinearMap.ext fun r ↦ by
              change r_hom.hom (r • m₀) = r
              rw [r_hom.hom.map_smul, hr_apply, smul_eq_mul, mul_one] }⟩

/-- **Eisenbud's projective-summand criterion.** Let `w` be a non-zero-divisor in a local ring `S`
with local quotient `R = S ⧸ (w)`, and let `X` be a finite-projective matrix factorization of `w`.
The odd-to-even differential `d₁` has image in `𝔪_S • X₀` if and only if the reduced cokernel of
`X` has no nonzero projective `R`-retract. -/
theorem range_d₁_le_maximalIdeal_smul_iff_forall_projective_retract_isZero
    (hw : w ∈ nonZeroDivisors S) (X : MatrixFactorization S w) :
    LinearMap.range X.obj.d₁.hom.hom ≤ maximalIdeal S • ⊤ ↔
      ∀ P : ModuleCat.{u} (S ⧸ Ideal.span {w}), Projective P →
        Nonempty (Retract P
          (cokernelFunctor.obj
            ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj) →
        IsZero P := by
  refine ⟨fun hd₁ P _ ⟨ret⟩ ↦ isZero_projective_retract_of_range_d₁_le hw hd₁ P ret, fun h ↦ ?_⟩
  by_contra hnot
  have hzero := h (ModuleCat.of (S ⧸ Ideal.span {w}) (S ⧸ Ideal.span {w})) inferInstance
    (nonempty_retract_self_of_not_range_d₁_le hnot)
  exact not_subsingleton (S ⧸ Ideal.span {w}) (ModuleCat.subsingleton_of_isZero hzero)

/-- **Minimality of Eisenbud's matrix factorization.** Let `0 → P --f--> Q --g--> M → 0` be a
minimal length-one `S`-projective resolution (`range f ≤ 𝔪_S • Q`) of an `S ⧸ (w)`-module `M`, for
a non-zero-divisor `w` with local quotient `S ⧸ (w)`. The attached matrix factorization
`ofInjective f` is minimal if and only if `M` has no nonzero projective `S ⧸ (w)`-retract. -/
theorem isMinimal_ofInjective_iff (hw : w ∈ nonZeroDivisors S)
    {P Q : FGModuleCat.{u} S} [Module.Projective S P] [Module.Projective S Q]
    {M : ModuleCat.{u} (S ⧸ Ideal.span {w})} {f : P ⟶ Q}
    {g : Q.obj ⟶ (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M}
    (hf : Function.Injective f.hom.hom) (hfg : Function.Exact f.hom.hom g.hom)
    (hg : Function.Surjective g) (hf_min : LinearMap.range f.hom.hom ≤ maximalIdeal S • ⊤) :
    (ofInjective f hf (hfg.smul_mem_range (Ideal.Quotient.mk_singleton_self w))).IsMinimal ↔
      ∀ R_proj : ModuleCat.{u} (S ⧸ Ideal.span {w}), Projective R_proj →
        Nonempty (Retract R_proj M) → IsZero R_proj := by
  rw [isMinimal_iff_range_le_maximalIdeal_smul,
    range_d₁_le_maximalIdeal_smul_iff_forall_projective_retract_isZero hw,
    and_iff_right (show LinearMap.range
      (ofInjective f hf (hfg.smul_mem_range (Ideal.Quotient.mk_singleton_self w))).obj.d₀.hom.hom ≤
      maximalIdeal S • ⊤ from hf_min)]
  let e := quotientCokernelIsoOfExact hf hfg hg
  refine forall₂_congr fun R_proj _ ↦ imp_congr_left ⟨?_, ?_⟩
  · exact fun ⟨ret⟩ ↦ ⟨ret.trans e.retract⟩
  · exact fun ⟨ret⟩ ↦ ⟨ret.trans e.symm.retract⟩

end ProjectiveRetract

end TauCeti.MatrixFactorization
