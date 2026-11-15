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
(`TauCeti.MatrixFactorization.IsMinimal`) if both differentials land in `Ring.jacobson S • ⊤`. When
`(S, 𝔪)` and `R = S ⧸ (w)` are local, reducing modulo `w` preserves and reflects minimality, and for
`w ∈ nonZeroDivisors S`, `range d₁ ≤ 𝔪 • X₀` holds iff the reduced cokernel has no nonzero
projective `R`-retract (`range_d₁_le_maximalIdeal_smul_iff_forall_projective_retract_isZero`,
`isMinimal_ofInjective_iff`).

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Sections 5–6.
-/

public section
noncomputable section

universe u

open CategoryTheory Limits IsLocalRing
open scoped TensorProduct ChangeOfRings

section QuotientMinimal

variable {S : Type u} [CommRing S] [IsLocalRing S] {w : S} [IsLocalRing (S ⧸ Ideal.span {w})]

/-- Over a local ring `S` with local quotient `R = S ⧸ (w)`, a pure tensor `1 ⊗ m` in `R ⊗[S] M`
lies in `𝔪_R • ⊤` if and only if `m` lies in `𝔪_S • ⊤`. -/
theorem TensorProduct.one_tmul_mem_maximalIdeal_smul_top_iff {M : Type*} [AddCommGroup M]
    [Module S M] (m : M) :
    (1 : S ⧸ Ideal.span {w}) ⊗ₜ[S] m ∈
        (maximalIdeal (S ⧸ Ideal.span {w}) • ⊤ :
          Submodule (S ⧸ Ideal.span {w}) ((S ⧸ Ideal.span {w}) ⊗[S] M)) ↔
      m ∈ (maximalIdeal S • ⊤ : Submodule S M) := by
  let q := Ideal.Quotient.mk (Ideal.span {w})
  have hloc : IsLocalHom q := .of_surjective _ Ideal.Quotient.mk_surjective
  have hmax : (maximalIdeal S).map q = maximalIdeal (S ⧸ Ideal.span {w}) :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hwm : w ∈ maximalIdeal S :=
    TauCeti.IsLocalRing.mem_maximalIdeal_of_isLocalRing_quotient_span_singleton
  constructor
  · intro hm
    obtain ⟨z, hz, heq⟩ : ∃ z ∈ (maximalIdeal S • ⊤ : Submodule S M),
        (1 : S ⧸ Ideal.span {w}) ⊗ₜ[S] z = (1 : S ⧸ Ideal.span {w}) ⊗ₜ[S] m :=
      Submodule.smul_induction_on hm
        (fun r hr t _ ↦ by
          obtain ⟨s, hs, rfl⟩ := (Ideal.mem_map_iff_of_surjective _
            Ideal.Quotient.mk_surjective).1 (hmax.symm ▸ hr)
          obtain ⟨x, rfl⟩ := TensorProduct.exists_one_tmul_eq (Ideal.span {w}) t
          exact ⟨s • x, Submodule.smul_mem_smul hs Submodule.mem_top,
            (TensorProduct.smul_tmul s (1 : S ⧸ Ideal.span {w}) x).symm⟩)
        (fun _ _ ⟨z₁, hz₁, h₁⟩ ⟨z₂, hz₂, h₂⟩ ↦
          ⟨z₁ + z₂, add_mem hz₁ hz₂, by rw [TensorProduct.tmul_add, h₁, h₂]⟩)
    obtain ⟨y, hy⟩ := (TensorProduct.one_tmul_eq_zero_iff_exists_smul_eq w (m - z)).1
      (by rw [TensorProduct.tmul_sub, sub_eq_zero]; exact heq.symm)
    exact add_sub_cancel z m ▸ add_mem hz (hy ▸ Submodule.smul_mem_smul hwm Submodule.mem_top)
  · exact fun hm ↦ Submodule.smul_induction_on hm
      (fun s hs x _ ↦ by
        rw [(TensorProduct.smul_tmul s (1 : S ⧸ Ideal.span {w}) x).symm.trans
          (TensorProduct.smul_tmul' (q s) (1 : S ⧸ Ideal.span {w}) x).symm]
        exact Submodule.smul_mem_smul (map_nonunit q s hs) Submodule.mem_top)
      (fun _ _ hx hy ↦ by rw [TensorProduct.tmul_add]; exact add_mem hx hy)

/-- Extending scalars along `S → S ⧸ (w)` preserves and reflects the maximal-ideal range condition
on module morphisms. -/
theorem ModuleCat.range_extendScalars_quotient_le_maximalIdeal_smul_iff
    {P Q : ModuleCat.{u} S} (g : P ⟶ Q) :
    LinearMap.range
        (((ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {w}))).map g).hom) ≤
      maximalIdeal (S ⧸ Ideal.span {w}) • ⊤ ↔
      LinearMap.range g.hom ≤ maximalIdeal S • ⊤ := by
  let q := Ideal.Quotient.mk (Ideal.span {w})
  refine ⟨?_, ?_⟩
  · rintro hg _ ⟨x, rfl⟩
    exact (TensorProduct.one_tmul_mem_maximalIdeal_smul_top_iff _).1
      (hg ⟨(1 : S ⧸ Ideal.span {w}) ⊗ₜ[S, q] x, ModuleCat.ExtendScalars.map_tmul q g 1 x⟩)
  · rintro hg _ ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := TensorProduct.exists_one_tmul_eq (M := P) (Ideal.span {w}) z
    change ((ModuleCat.extendScalars q).map g) ((1 : S ⧸ Ideal.span {w}) ⊗ₜ[S, q] x) ∈ _
    rw [ModuleCat.ExtendScalars.map_tmul]
    exact (TensorProduct.one_tmul_mem_maximalIdeal_smul_top_iff _).2 (hg ⟨x, rfl⟩)

end QuotientMinimal

namespace TauCeti.MatrixFactorization

variable {S : Type u} [CommRing S] {w : S}

/-- A matrix factorization `X = (X₀ --d₀--> X₁ --d₁--> X₀)` over `S` is *minimal* if both
differentials have image in `Ring.jacobson S • ⊤`. -/
def IsMinimal (X : MatrixFactorization S w) : Prop :=
  LinearMap.range X.obj.d₀.hom.hom ≤ Ring.jacobson S • ⊤ ∧
    LinearMap.range X.obj.d₁.hom.hom ≤ Ring.jacobson S • ⊤

/-- Unfolds `TauCeti.MatrixFactorization.IsMinimal`. -/
theorem isMinimal_iff (X : MatrixFactorization S w) :
    X.IsMinimal ↔ LinearMap.range X.obj.d₀.hom.hom ≤ Ring.jacobson S • ⊤ ∧
      LinearMap.range X.obj.d₁.hom.hom ≤ Ring.jacobson S • ⊤ := Iff.rfl

/-- Over a local ring, minimality means both differentials map into `maximalIdeal S • ⊤`. -/
theorem isMinimal_iff_range_le_maximalIdeal_smul [IsLocalRing S] (X : MatrixFactorization S w) :
    X.IsMinimal ↔ LinearMap.range X.obj.d₀.hom.hom ≤ maximalIdeal S • ⊤ ∧
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
    simpa [Category.assoc, hf₁] using congrArg (fun m ↦ m.hom ≫ e.hom.hom.f₁.hom) e.inv.hom.comm₀
  have comm₁ : e.inv.hom.f₁.hom ≫ X.obj.d₁.hom ≫ e.hom.hom.f₀.hom = Y.obj.d₁.hom := by
    simpa [Category.assoc, hf₀] using congrArg (fun m ↦ m.hom ≫ e.hom.hom.f₀.hom) e.inv.hom.comm₁
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, rfl⟩; rw [← comm₀]
    exact Submodule.smul_top_le_comap_smul_top _ e.hom.hom.f₁.hom.hom (hX.1 ⟨_, rfl⟩)
  · rintro _ ⟨y, rfl⟩; rw [← comm₁]
    exact Submodule.smul_top_le_comap_smul_top _ e.hom.hom.f₀.hom.hom (hX.2 ⟨_, rfl⟩)

/-- Isomorphic matrix factorizations are simultaneously minimal. -/
theorem isMinimal_of_iso_iff {X Y : MatrixFactorization S w} (e : X ≅ Y) :
    X.IsMinimal ↔ Y.IsMinimal := ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

/-- Parity shift preserves and reflects minimality. -/
@[simp]
theorem isMinimal_parityShift_iff (X : MatrixFactorization S w) :
    (parityShift.obj X).IsMinimal ↔ X.IsMinimal := by
  have hd₀ : (-X.obj.d₁).hom.hom = -X.obj.d₁.hom.hom := rfl
  have hd₁ : (-X.obj.d₀).hom.hom = -X.obj.d₀.hom.hom := rfl
  rw [isMinimal_iff, isMinimal_iff, parityShift_obj_d₀, parityShift_obj_d₁, hd₀, hd₁,
    LinearMap.range_neg, LinearMap.range_neg, and_comm]

section LocalReduction

variable [IsLocalRing S] [IsLocalRing (S ⧸ Ideal.span {w})]

/-- Over a local ring `S` with local quotient `S ⧸ (w)`, the reduced two-periodic complex of `X`
is minimal if and only if `X` is minimal. -/
theorem quotientPeriodicComplex_obj_isMinimal_iff (X : MatrixFactorization S w) :
    (quotientPeriodicComplex.obj X).IsMinimal ↔ X.IsMinimal := by
  rw [HomologicalComplex.isMinimal_iff_forall_rel, isMinimal_iff_range_le_maximalIdeal_smul,
    ringJacobson_eq_maximalIdeal]
  refine ⟨fun h ↦ ⟨(ModuleCat.range_extendScalars_quotient_le_maximalIdeal_smul_iff _).1
      (h 0 1 (zero_add 1)),
    (ModuleCat.range_extendScalars_quotient_le_maximalIdeal_smul_iff _).1 (h 1 0 (by decide))⟩,
    fun ⟨hd₀, hd₁⟩ i j hij ↦ ?_⟩
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) i with rfl | rfl
  · obtain rfl : j = 1 := hij.symm.trans (zero_add 1)
    exact (ModuleCat.range_extendScalars_quotient_le_maximalIdeal_smul_iff _).2 hd₀
  · obtain rfl : j = 0 := hij.symm.trans (by decide)
    exact (ModuleCat.range_extendScalars_quotient_le_maximalIdeal_smul_iff _).2 hd₁

/-- Unfolding the reduced two-periodic complex of `X` from any starting parity `j : ℤ` gives a
minimal chain complex over `S ⧸ (w)` if and only if `X` is minimal. -/
theorem resolutionComplex_quotientPeriodicComplex_isMinimal_iff (X : MatrixFactorization S w)
    (j : ℤ) :
    (PeriodicComplex.resolutionComplex (quotientPeriodicComplex.obj X) j).IsMinimal ↔
      X.IsMinimal := by
  let Q := quotientPeriodicComplex.obj X
  rw [← quotientPeriodicComplex_obj_isMinimal_iff, ChainComplex.isMinimal_iff_range_d_succ_le,
    HomologicalComplex.isMinimal_iff_forall_rel]
  refine ⟨fun h a b hab ↦ ?_, fun h k ↦ ?_⟩
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, ((j - k : ℤ) : ZMod 2) = b := by
      rcases (by decide : ∀ x y : ZMod 2, x = y ∨ x = y - 1) b (j : ZMod 2) with rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by push_cast; ring⟩
    have hk' : ((j - (k + 1 : ℕ) : ℤ) : ZMod 2) = a :=
      add_right_cancel ((show ((j - (k + 1 : ℕ) : ℤ) : ZMod 2) + 1 = ((j - k : ℤ) : ZMod 2) by
        push_cast; ring).trans (hk.trans hab.symm))
    subst hk hk'
    rintro _ ⟨x, rfl⟩
    exact PeriodicComplex.resolutionComplex_d Q j k ▸ h k ⟨x, rfl⟩
  · rw [PeriodicComplex.resolutionComplex_d]
    exact h _ _ (show ((j - (k + 1 : ℕ) : ℤ) : ZMod 2) + 1 = ((j - k : ℤ) : ZMod 2) by
      push_cast; ring)

/-- For a non-zero-divisor `w`, the periodic projective resolution of the reduced cokernel of `X`
is minimal if and only if `X` is minimal. -/
theorem quotientCokernelProjectiveResolution_complex_isMinimal_iff (hw : w ∈ nonZeroDivisors S)
    (X : MatrixFactorization S w) :
    (quotientCokernelProjectiveResolution hw X).complex.IsMinimal ↔ X.IsMinimal :=
  resolutionComplex_quotientPeriodicComplex_isMinimal_iff X 1

end LocalReduction

section ProjectiveRetract

variable [IsLocalRing S] [IsLocalRing (S ⧸ Ideal.span {w})]

omit [IsLocalRing S] in
private theorem nonempty_retract_self_of_nontrivial_projective_retract
    {M P : ModuleCat.{u} (S ⧸ Ideal.span {w})} [Module.Finite (S ⧸ Ideal.span {w}) M]
    [Projective P] [Nontrivial P] (ret : Retract P M) :
    Nonempty (Retract (ModuleCat.of (S ⧸ Ideal.span {w}) (S ⧸ Ideal.span {w})) M) := by
  let R := S ⧸ Ideal.span {w}
  have : Module.Finite R P := .of_surjective ret.r.hom
    (Function.LeftInverse.surjective fun p ↦ ConcreteCategory.congr_hom ret.retract p)
  have : Module.Projective R P := (IsProjective.iff_projective P).2 inferInstance
  have : Module.Free R P := Module.free_of_projective_of_isLocalRing
  let b := Module.Free.chooseBasis R P
  obtain ⟨i₀⟩ : Nonempty (Module.Free.ChooseBasisIndex R P) := by
    by_contra! hemp; exact not_subsingleton P b.repr.subsingleton
  let _ := Classical.decEq (Module.Free.ChooseBasisIndex R P)
  refine ⟨Retract.trans
    { i := ModuleCat.ofHom (LinearMap.toSpanSingleton R P (b i₀))
      r := ModuleCat.ofHom (b.coord i₀)
      retract := ModuleCat.hom_ext <| LinearMap.ext fun r ↦ by
        change b.coord i₀ (r • b i₀) = r
        rw [map_smul, b.coord_apply, b.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one] }
    ret⟩

private theorem not_nonempty_retract_self_of_range_d₁_le (hw : w ∈ nonZeroDivisors S)
    {X : MatrixFactorization S w} (hd₁ : LinearMap.range X.obj.d₁.hom.hom ≤ maximalIdeal S • ⊤)
    (retR : Retract (ModuleCat.of (S ⧸ Ideal.span {w}) (S ⧸ Ideal.span {w}))
      (cokernelFunctor.obj
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj) :
    False := by
  let q := Ideal.Quotient.mk (Ideal.span {w})
  obtain ⟨y, hy⟩ := quotientCokernelπ_surjective X (retR.i.hom 1)
  have hπy : retR.r.hom (quotientCokernelπ X y) = 1 :=
    hy ▸ ConcreteCategory.congr_hom retR.retract 1
  have : Module.Projective S X.obj.X₁ := X.property.2
  let φ : X.obj.X₁ →ₗ[S] S ⧸ Ideal.span {w} :=
    (quotientCokernelπ X ≫ (ModuleCat.restrictScalars q).map retR.r).hom
  obtain ⟨β, hβ⟩ := Module.projective_lifting_property (Ideal.span {w}).mkQ φ
    (Submodule.mkQ_surjective _)
  have hβ_eq (z : X.obj.X₁) : q (β z) = φ z := congr($hβ z)
  have hβy : β y ∉ maximalIdeal S := fun hm ↦ by
    have : IsLocalHom q := .of_surjective _ Ideal.Quotient.mk_surjective
    have h1 : (1 : S ⧸ Ideal.span {w}) ∈ maximalIdeal (S ⧸ Ideal.span {w}) := by
      have hφy : φ y = 1 := hπy
      rw [← hφy, ← hβ_eq y]; exact map_nonunit q (β y) hm
    exact (maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hd₀_div (x : X.obj.X₀) : ∃ c : S, β (X.obj.d₀.hom.hom x) = w * c := by
    refine Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 ?_)
    rw [hβ_eq]
    change ((ModuleCat.restrictScalars q).map retR.r).hom
      ((quotientCokernelπ X).hom (X.obj.d₀.hom.hom x)) = 0
    rw [(exact_d₀_quotientCokernelπ X _).2 ⟨x, rfl⟩, map_zero]
  obtain ⟨m, hm, hwm_eq⟩ : ∃ m ∈ maximalIdeal S,
      β (X.obj.d₀.hom.hom (X.obj.d₁.hom.hom y)) = w * m :=
    Submodule.smul_induction_on (hd₁ ⟨y, rfl⟩)
      (fun a ha x₀ _ ↦ by
        obtain ⟨c, hc⟩ := hd₀_div x₀
        exact ⟨a * c, Ideal.mul_mem_right c _ ha, by
          rw [map_smul, map_smul, smul_eq_mul, hc]; ring⟩)
      (fun _ _ ⟨m₁, hm₁, h₁⟩ ⟨m₂, hm₂, h₂⟩ ↦
        ⟨m₁ + m₂, add_mem hm₁ hm₂, by rw [map_add, map_add, h₁, h₂, mul_add]⟩)
  have hwy : w * β y = w * m := by
    rw [← smul_eq_mul, ← β.map_smul, ← d₁_comp_d₀_apply, hwm_eq]
  exact hβy ((Module.Flat.isSMulRegular_of_nonZeroDivisors hw hwy) ▸ hm)

private theorem isZero_projective_retract_of_range_d₁_le (hw : w ∈ nonZeroDivisors S)
    {X : MatrixFactorization S w} (hd₁ : LinearMap.range X.obj.d₁.hom.hom ≤ maximalIdeal S • ⊤)
    (P : ModuleCat.{u} (S ⧸ Ideal.span {w})) [Projective P]
    (ret : Retract P (cokernelFunctor.obj
      ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj) : IsZero P := by
  cases subsingleton_or_nontrivial P
  · exact ModuleCat.isZero_of_subsingleton P
  · obtain ⟨retR⟩ := nonempty_retract_self_of_nontrivial_projective_retract ret
    exact False.elim (not_nonempty_retract_self_of_range_d₁_le hw hd₁ retR)

omit [IsLocalRing (S ⧸ Ideal.span {w})] in
private theorem exists_linearMap_eq_one_of_not_mem_maximalIdeal_smul {P : Type u} [AddCommGroup P]
    [Module S P] [Module.Projective S P] {x : P} (hx : x ∉ (maximalIdeal S • ⊤ : Submodule S P)) :
    ∃ α : P →ₗ[S] S, α x = 1 := by
  obtain ⟨φ₀, hφ₀⟩ := TauCeti.IsLocalRing.exists_linearMap_quotient_eq_one hx
  obtain ⟨α₀, hα₀⟩ := Module.projective_lifting_property (maximalIdeal S).mkQ φ₀
    (Submodule.mkQ_surjective _)
  have hu : IsUnit (α₀ x) := notMem_maximalIdeal.1 fun hm ↦ zero_ne_one <| by
    rw [← (Submodule.Quotient.mk_eq_zero _).2 hm, ← Submodule.mkQ_apply,
      ← LinearMap.comp_apply, hα₀, hφ₀]
  exact ⟨((hu.unit⁻¹ : Sˣ) : S) • α₀, hu.val_inv_mul⟩

omit [IsLocalRing (S ⧸ Ideal.span {w})] in
private theorem nonempty_retract_self_of_not_range_d₁_le
    {X : MatrixFactorization S w} (hnot : ¬ LinearMap.range X.obj.d₁.hom.hom ≤ maximalIdeal S • ⊤) :
    Nonempty (Retract (ModuleCat.of (S ⧸ Ideal.span {w}) (S ⧸ Ideal.span {w}))
      (cokernelFunctor.obj
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj) := by
  let q := Ideal.Quotient.mk (Ideal.span {w})
  let X' := (baseChangeFunctor q).obj X
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := Set.not_subset.1 hnot
  have : Module.Projective S X.obj.X₀ := X.property.1
  obtain ⟨α, hαy⟩ := exists_linearMap_eq_one_of_not_mem_maximalIdeal_smul hy
  let R_mod := ModuleCat.of (S ⧸ Ideal.span {w}) (S ⧸ Ideal.span {w})
  let g : X.obj.X₀.obj ⟶ (ModuleCat.restrictScalars q).obj R_mod :=
    ModuleCat.ofHom (X := X.obj.X₀.obj) (Y := (ModuleCat.restrictScalars q).obj R_mod)
      ((Ideal.span {w}).mkQ ∘ₗ α)
  let r_hom : (cokernelFunctor.obj X').obj ⟶ R_mod :=
    (cokernelDesc (Ideal.Quotient.mk_singleton_self w) X').hom ≫
      ((ModuleCat.extendRestrictScalarsAdj.{u} q).homEquiv _ _).symm g
  let m₀ : (cokernelFunctor.obj X').obj := quotientCokernelπ X y
  have hr_apply : r_hom.hom m₀ = 1 := by
    have hcomp : cokernelπ X' ≫ r_hom =
        ((ModuleCat.extendRestrictScalarsAdj.{u} q).homEquiv _ _).symm (X.obj.d₁.hom ≫ g) :=
      (cokernelπ_cokernelDesc_hom_assoc (Ideal.Quotient.mk_singleton_self w) X' _).trans
        (Adjunction.homEquiv_naturality_left_symm
          (ModuleCat.extendRestrictScalarsAdj.{u} q) X.obj.d₁.hom g).symm
    refine (congrArg r_hom.hom (quotientCokernelπ_apply X y)).trans
      ((ConcreteCategory.congr_hom hcomp _).trans ?_)
    refine (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply (M := X.obj.X₁.obj) _ y).symm.trans ?_
    rw [Equiv.apply_symm_apply]; change q (α (X.obj.d₁.hom.hom y)) = 1; rw [hαy, map_one]
  exact ⟨{ i := ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ m₀), r := r_hom,
           retract := ModuleCat.hom_ext <| LinearMap.ext fun r ↦ by
             change r_hom.hom (r • m₀) = r
             rw [r_hom.hom.map_smul, hr_apply, smul_eq_mul, mul_one] }⟩

/-- **Eisenbud's projective-summand criterion.** For a non-zero-divisor `w` in a local ring `S`
with local quotient `R = S ⧸ (w)`, `range d₁ ≤ 𝔪_S • X₀` holds if and only if the reduced cokernel
of `X` has no nonzero projective `R`-retract. -/
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
  exact not_subsingleton (S ⧸ Ideal.span {w}) <| ModuleCat.subsingleton_of_isZero <|
    h (ModuleCat.of _ (S ⧸ Ideal.span {w})) inferInstance
      (nonempty_retract_self_of_not_range_d₁_le hnot)

/-- **Minimality of Eisenbud's matrix factorization.** For a minimal length-one `S`-projective
resolution `0 → P --f--> Q --g--> M → 0` of an `S ⧸ (w)`-module `M`, `ofInjective f` is minimal if
and only if `M` has no nonzero projective `S ⧸ (w)`-retract. -/
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
  exact forall₂_congr fun _ _ ↦ imp_congr_left
    ⟨fun ⟨ret⟩ ↦ ⟨ret.trans e.retract⟩, fun ⟨ret⟩ ↦ ⟨ret.trans e.symm.retract⟩⟩

end ProjectiveRetract
end TauCeti.MatrixFactorization
