/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.AuslanderBridgerSequence
public import TauCeti.CategoryTheory.ObjectProperty.Syzygy

/-!
# `k`-torsionfree modules are `k`-th syzygies

Let `A` be a right Noetherian ring and `M` a left `A`-module with a presentation `P₁ ⟶ P₀ ⟶ M ⟶ 0`
by finitely generated projective modules, with transpose `Tr M`. Following Auslander and Bridger,
`M` is **`k`-torsionfree** when `Ext^i(Tr M, A) = 0` for `1 ≤ i ≤ k`. This file proves that a
`k`-torsionfree module is a `k`-th syzygy: there is an exact sequence `0 ⟶ M ⟶ Q₁ ⟶ ⋯ ⟶ Q_k` with
every `Qᵢ` finitely generated projective (`CategoryTheory.ObjectProperty.IsSyzygy`). So vanishing of
`Ext^i(Tr M, A)` in degrees `1, …, k`, which does not depend on the presentation since `Tr M` is
determined up to projective summands, produces `k` steps of a finite projective coresolution of
`M`. For `k = 1` this says
that torsionless modules embed in finitely generated free modules, and for `k = 2` that reflexive
modules (`TauCeti.opDualEval_bijective_iff_ext_eq_zero`) are second syzygies.

## Main results

* `TauCeti.AuslanderReitenTranspose.isSyzygy_of_ext_eq_zero`: a `k`-torsionfree module is a `k`-th
  syzygy.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969), Theorem 2.17.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian

universe w u

variable {A : Type u} [Ring A] {P₀ P₁ M Q : Type u} [AddCommGroup P₀] [Module A P₀]
  [AddCommGroup P₁] [Module A P₁] [AddCommGroup M] [Module A M] [AddCommGroup Q] [Module A Q]
  {p : P₁ →ₗ[A] P₀} {π : P₀ →ₗ[A] M}

/-- For a map `j : M ⟶ Q` whose dual is surjective, the transpose of the presentation
`P₀ ⟶ Q ⟶ Q ⧸ j(M)` is the image of `p* : P₀* ⟶ P₁*`. -/
private noncomputable def transposeCompEquiv (hexact : Function.Exact p π)
    (hπ : Function.Surjective π) (j : M →ₗ[A] Q)
    (hj : Function.Surjective (j.lcomp Aᵐᵒᵖ A)) :
    AuslanderReitenTranspose (j ∘ₗ π) ≃ₗ[Aᵐᵒᵖ] LinearMap.range (p.lcomp Aᵐᵒᵖ A) := by
  refine LinearEquiv.ofBijective (AuslanderReitenTranspose.lift (j ∘ₗ π)
    (N := LinearMap.range (p.lcomp Aᵐᵒᵖ A)) (p.lcomp Aᵐᵒᵖ A).rangeRestrict fun ψ ↦ ?_) ⟨?_, ?_⟩
  · -- `ψ ∘ j ∘ π` vanishes on the image of `p`.
    refine Subtype.ext (LinearMap.ext fun x ↦ ?_)
    simp [hexact.apply_apply_eq_zero]
  · refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
    induction x using AuslanderReitenTranspose.induction_on with
    | h φ =>
      rw [AuslanderReitenTranspose.lift_mk, ← LinearMap.mem_ker, LinearMap.ker_rangeRestrict,
        (hexact.lcomp_of_surjective (T := Aᵐᵒᵖ) A hπ).linearMap_ker_eq] at hx
      obtain ⟨χ, rfl⟩ := hx
      obtain ⟨ψ, rfl⟩ := hj χ
      exact (AuslanderReitenTranspose.mk_eq_zero_iff _ _).2 ⟨ψ, rfl⟩
  · intro y
    obtain ⟨φ, rfl⟩ := (p.lcomp Aᵐᵒᵖ A).surjective_rangeRestrict y
    exact ⟨AuslanderReitenTranspose.mk _ φ, AuslanderReitenTranspose.lift_mk _ _ _ _⟩

section Ext

variable [HasExt.{w} (ModuleCat.{u} Aᵐᵒᵖ)]

/-- If `Ext^{i+1}(Tr M, A)` vanishes for `2 ≤ i + 1 ≤ k + 1`, then `Ext^i` of the transpose of
`P₀ ⟶ Q ⟶ Q ⧸ j(M)` vanishes for `1 ≤ i ≤ k`: that transpose is the image `K` of `p*`, and
`0 ⟶ K ⟶ P₁* ⟶ Tr M ⟶ 0` shifts the degree by one. -/
private lemma ext_transpose_comp_eq_zero [Module.Finite A P₁] [Module.Projective A P₁]
    (hexact : Function.Exact p π) (hπ : Function.Surjective π) (j : M →ₗ[A] Q)
    (hj : Function.Surjective (j.lcomp Aᵐᵒᵖ A)) (k : ℕ)
    (hext : ∀ i, 0 < i → i ≤ k + 1 → ∀ e : Ext.{w}
      (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose p)) (ModuleCat.of Aᵐᵒᵖ A) i, e = 0)
    (i : ℕ) (hi : 0 < i) (hik : i ≤ k) (e : Ext.{w}
      (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose (j ∘ₗ π))) (ModuleCat.of Aᵐᵒᵖ A) i) :
    e = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by lia⟩
  let eq := transposeCompEquiv hexact hπ j hj
  -- `LinearEquiv.toModuleIso` does not apply: the module structure of the transpose is stated over
  -- `MulOpposite.instSemiring`, and `AuslanderReitenTranspose` is not exposed, so it cannot be
  -- identified with the structure over `Ring.toSemiring` that `ModuleCat.of` uses.
  let φ : ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose (j ∘ₗ π)) ≅
      ModuleCat.of Aᵐᵒᵖ (LinearMap.range (p.lcomp Aᵐᵒᵖ A)) :=
    { hom := ModuleCat.ofHom eq.toLinearMap
      inv := ModuleCat.ofHom eq.symm.toLinearMap
      hom_inv_id := ModuleCat.hom_ext (LinearMap.ext eq.symm_apply_apply)
      inv_hom_id := ModuleCat.hom_ext (LinearMap.ext eq.apply_symm_apply) }
  -- Transport `e` to the image `K` of `p*`, then shift it into `Ext^{m+2}(Tr M, A) = 0`.
  have hx : (Ext.mk₀ φ.inv).comp e (zero_add _) = 0 :=
    (precomp_extClass_bijective (AuslanderReitenTranspose.shortComplex_shortExact p)
      (ModuleCat.of Aᵐᵒᵖ A) m).1.eq_iff' (map_zero _) |>.1 (hext _ (by lia) (by lia) _)
  rw [← Ext.mk₀_id_comp e, ← φ.hom_inv_id, ← Ext.mk₀_comp_mk₀_assoc, hx, Ext.comp_zero]

variable (A) in
/-- The finitely generated projective left `A`-modules. -/
private abbrev finiteProjective : ObjectProperty (ModuleCat.{u} A) :=
  fun X ↦ Module.Finite A X ∧ Module.Projective A X

private lemma isSyzygy_of_ext_eq_zero_aux [IsNoetherianRing Aᵐᵒᵖ] (k : ℕ) :
    ∀ (P₀ P₁ M : Type u) [AddCommGroup P₀] [Module A P₀] [Module.Finite A P₀]
      [Module.Projective A P₀] [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁]
      [Module.Projective A P₁] [AddCommGroup M] [Module A M] (p : P₁ →ₗ[A] P₀)
      (π : P₀ →ₗ[A] M), Function.Exact p π → Function.Surjective π →
      (∀ i, 0 < i → i ≤ k → ∀ e : Ext.{w}
        (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose p)) (ModuleCat.of Aᵐᵒᵖ A) i, e = 0) →
      (finiteProjective A).IsSyzygy k (ModuleCat.of A M) := by
  induction k with
  | zero => exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ↦ ObjectProperty.isSyzygy_zero _ _
  | succ k ih =>
    -- Embed `M` into `Aⁿ` through generators of `M*`. The cokernel `N` has the presentation
    -- `P₀ ⟶ Aⁿ ⟶ N ⟶ 0`, whose transpose is the image `K` of `P₀* ⟶ P₁*`; the sequence
    -- `0 ⟶ K ⟶ P₁* ⟶ Tr M ⟶ 0` shifts `Ext^i(K, A)` to `Ext^{i+1}(Tr M, A)`, so `N` is
    -- `k`-torsionfree and the induction applies.
    intro P₀ P₁ M _ _ _ _ _ _ _ _ _ _ p π hexact hπ hext
    -- `M` is torsionless, and `M*` is finitely generated since `A` is right Noetherian.
    have hinj : Function.Injective (opDualEval A M) :=
      (opDualEval_injective_iff_ext_one_eq_zero.{w} hexact hπ).2 (hext 1 one_pos (by lia))
    have : Module.Finite Aᵐᵒᵖ (Module.Dual A M) :=
      Module.Finite.of_injective (π.lcomp Aᵐᵒᵖ A) (LinearMap.lcomp_injective_of_surjective π hπ)
    -- Generators `s i` of `M*` give `j : M ⟶ Aⁿ`, injective with surjective dual.
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := Aᵐᵒᵖ) (M := Module.Dual A M)
    let j : M →ₗ[A] Fin n → A := LinearMap.pi s
    have hj : Function.Surjective (j.lcomp Aᵐᵒᵖ A) := by
      rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨LinearMap.proj i, rfl⟩
    have hjinj : Function.Injective j := fun m m' h ↦ hinj <| LinearMap.ext fun φ ↦ by
      obtain ⟨ψ, rfl⟩ := hj φ
      simp only [opDualEval_apply, LinearMap.lcomp_apply, h]
    -- The cokernel `N` of `j` is `k`-torsionfree, hence a `k`-th syzygy.
    have hN := ih (Fin n → A) P₀ ((Fin n → A) ⧸ LinearMap.range j) (j ∘ₗ π)
      (LinearMap.range j).mkQ ?_ (Submodule.mkQ_surjective _)
      (ext_transpose_comp_eq_zero hexact hπ j hj k hext)
    · have hzero : ModuleCat.ofHom j ≫ ModuleCat.ofHom (LinearMap.range j).mkQ = 0 :=
        ModuleCat.hom_ext (LinearMap.ext fun m ↦ (Submodule.Quotient.mk_eq_zero _).2
          (LinearMap.mem_range_self j m))
      refine (ObjectProperty.isSyzygy_succ_iff _ k _).2 ⟨ShortComplex.mk _ _ hzero, ?_,
        ⟨Iso.refl _⟩, ⟨inferInstanceAs (Module.Finite A (Fin n → A)),
          inferInstanceAs (Module.Projective A (Fin n → A))⟩, hN⟩
      · refine .mk' (ShortComplex.Exact.moduleCat_of_range_eq_ker _ _ ?_) ?_ ?_
        · simp
        · exact (ModuleCat.mono_iff_injective _).2 hjinj
        · exact (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)
    · rw [LinearMap.exact_iff, Submodule.ker_mkQ, LinearMap.range_comp_of_range_eq_top _
        (LinearMap.range_eq_top.2 hπ)]

/-- **`k`-torsionfree modules are `k`-th syzygies** (Auslander-Bridger): over a right Noetherian
ring `A`, if `M` has a presentation `P₁ ⟶ P₀ ⟶ M ⟶ 0` by finitely generated projective modules
and `Ext^i(Tr M, A) = 0` for `1 ≤ i ≤ k`, then there is an exact sequence
`0 ⟶ M ⟶ Q₁ ⟶ ⋯ ⟶ Q_k` with every `Qᵢ` finitely generated projective. -/
theorem AuslanderReitenTranspose.isSyzygy_of_ext_eq_zero [IsNoetherianRing Aᵐᵒᵖ]
    [Module.Finite A P₀] [Module.Projective A P₀] [Module.Finite A P₁] [Module.Projective A P₁]
    (hexact : Function.Exact p π) (hπ : Function.Surjective π) (k : ℕ)
    (hext : ∀ i, 0 < i → i ≤ k → ∀ e : Ext.{w}
      (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose p)) (ModuleCat.of Aᵐᵒᵖ A) i, e = 0) :
    ObjectProperty.IsSyzygy (fun X : ModuleCat.{u} A ↦ Module.Finite A X ∧ Module.Projective A X)
      k (ModuleCat.of A M) :=
  isSyzygy_of_ext_eq_zero_aux k P₀ P₁ M p π hexact hπ hext

end Ext

end TauCeti
