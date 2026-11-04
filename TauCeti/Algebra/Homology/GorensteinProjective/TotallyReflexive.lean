/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.TotallyAcyclic.Ext
public import TauCeti.Algebra.Homology.TotallyAcyclic.Splice
public import TauCeti.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Category.ModuleCat.Ext.Extension
public import TauCeti.LinearAlgebra.Dual.Reflexive
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt

/-!
# Totally reflexive modules

Let `A` be a ring. A finitely generated left `A`-module `M` is **totally reflexive** when
evaluation `M ⟶ M**` is bijective and `Ext^i(M, A) = 0` and `Ext^i(M*, A) = 0` for all `i > 0`.
Here `M* = Hom_A(M, A)` is a right `A`-module, that is, an `Aᵐᵒᵖ`-module, and `M**` is its
`A`-valued dual (`TauCeti.opDualEval`). Following Auslander and Bridger, over a left and right
noetherian ring these are exactly the Gorenstein-projective modules.

**Gorenstein-projective modules are totally reflexive**, over any ring. Let `P` be a complete
resolution of `M`.

* Every module of cycles `Zᵐ` of `P` is reflexive: it is the kernel of `Pᵐ ⟶ Pᵐ⁺¹`, every
  functional on it extends to `Pᵐ`, and finitely generated projective modules are reflexive
  (`TauCeti.opDualEval_bijective_of_exact`).
* `Ext^{>0}(M, A) = 0` is `TauCeti.IsGorensteinProjective.ext_eq_zero`.
* Dualizing `0 ⟶ Zᵐ ⟶ Pᵐ ⟶ Zᵐ⁺¹ ⟶ 0` gives a short exact sequence
  `0 ⟶ (Zᵐ⁺¹)* ⟶ (Pᵐ)* ⟶ (Zᵐ)* ⟶ 0` of right modules with projective middle term. A functional on
  `(Zᵐ⁺¹)*` is evaluation at some `z ∈ Zᵐ⁺¹` by reflexivity, so it extends to `(Pᵐ)*` as
  evaluation at a preimage of `z`. Hence `Ext¹((Zᵐ)*, A) = 0`, and dimension shifting gives
  `Ext^{>0}((Zᵐ)*, A) = 0` for every `m`.

**Totally reflexive modules are Gorenstein-projective** over a left and right noetherian ring.
A complete resolution is spliced from syzygies and cosyzygies
(`TauCeti.isGorensteinProjective_of_isCompleteResolutionStep`).

* Syzygies, using that `A` is left noetherian: a finitely generated module `X` with
  `Ext^{>0}(X, A) = 0` is a quotient `0 ⟶ X' ⟶ Aⁿ ⟶ X ⟶ 0` with `X'` of the same kind.
* Cosyzygies, using that `A` is right noetherian: for `M` totally reflexive, `M*` is finitely
  generated, and generators `φ₁, …, φₖ` give `j = (φᵢ) : M ⟶ Aᵏ`. Its dual `(Aᵏ)* ⟶ M*` is
  surjective, so `j` is injective as `M` is reflexive, and its cokernel `M'` is totally reflexive:
  the dual sequence `0 ⟶ M'* ⟶ (Aᵏ)* ⟶ M* ⟶ 0` is exact, `Ext` shifts along both sequences, and
  `M'` is reflexive by `TauCeti.opDualEval_bijective_of_exact_of_surjective`, using
  `Ext¹(M*, A) = 0`.

## Main definitions

* `TauCeti.IsTotallyReflexive`: totally reflexive modules.

## Main results

* `TauCeti.IsGorensteinProjective.isTotallyReflexive`: Gorenstein-projective modules are totally
  reflexive.
* `TauCeti.IsTotallyReflexive.isGorensteinProjective`: over a left and right noetherian ring,
  totally reflexive modules are Gorenstein-projective.
* `TauCeti.isTotallyReflexive_iff_isGorensteinProjective`: the two notions agree over a left and
  right noetherian ring.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969),
  Proposition (3.8): condition (c) there, `M` reflexive with `Ext^i(M, R) = Ext^i(M*, R) = 0` for
  `i > 0`, characterizes the modules of Gorenstein dimension zero.
* L. L. Avramov, A. Martsinkovsky, *Absolute, relative, and Tate cohomology of modules of finite
  Gorenstein dimension*, Proc. London Math. Soc. (3) 85 (2002), 393–440: §2, p. 398, for the
  name "totally reflexive" over a left and right noetherian ring, and Theorem 3.1 with `g = 0`,
  (i) ⇔ (iv), for the equivalence with having a complete resolution.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u

namespace TauCeti

variable (A : Type u) [Ring A]

/-- A finitely generated left `A`-module `M` is **totally reflexive** when evaluation into its
double dual is bijective and `Ext^{n+1}(M, A) = 0` and `Ext^{n+1}(M*, A) = 0` for every `n`, where
`M*` is the right module `Hom_A(M, A)`. -/
structure IsTotallyReflexive (M : ModuleCat.{u} A) : Prop where
  /-- A totally reflexive module is finitely generated. -/
  finite : Module.Finite A M
  /-- Evaluation `M ⟶ M**` is bijective. -/
  bijective_opDualEval : Function.Bijective (opDualEval A M)
  /-- `Ext^{n+1}(M, A) = 0`. -/
  ext_eq_zero (n : ℕ) (e : Ext.{u} M (ModuleCat.of A A) (n + 1)) : e = 0
  /-- `Ext^{n+1}(M*, A) = 0`. -/
  ext_dual_eq_zero (n : ℕ)
    (e : Ext.{u} (ModuleCat.of Aᵐᵒᵖ (Module.Dual A M)) (ModuleCat.of Aᵐᵒᵖ A) (n + 1)) : e = 0

variable {A}

end TauCeti

namespace CochainComplex.IsTotallyAcyclic

open TauCeti

variable {A : Type u} [Ring A] {P : CochainComplex (ModuleCat.{u} A) ℤ} (hP : P.IsTotallyAcyclic)
include hP

/-- A module isomorphic to the cycles of a totally acyclic complex is reflexive. -/
private theorem bijective_opDualEval (m : ℤ) {N : ModuleCat.{u} A} (e : N ≅ P.cycles m) :
    Function.Bijective (opDualEval A N) := by
  have := hP.finite m
  have := hP.finite (m + 1)
  have := hP.projective m
  have := hP.projective (m + 1)
  have hk : (ShortComplex.mk (e.hom ≫ P.iCycles m) (P.d m (m + 1)) (by simp)).Exact :=
    ShortComplex.exact_of_f_is_kernel _
      (IsLimit.ofIsoLimit (P.cyclesIsKernel m (m + 1) (by simp))
        (Fork.ext e.symm (by simp [Fork.ι])))
  refine opDualEval_bijective_of_exact A (ι := (e.hom ≫ P.iCycles m).hom)
    (g := (P.d m (m + 1)).hom) ((ModuleCat.mono_iff_injective _).1 inferInstance)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hk) (fun φ ↦ ?_)
    (opDualEval_bijective A _) (opDualEval_bijective A _).1
  obtain ⟨g, hg⟩ := hP.exists_extend_iCycles m (φ ∘ₗ e.inv.hom)
  refine ⟨g, LinearMap.ext fun x ↦ ?_⟩
  have := LinearMap.congr_fun hg (e.hom x)
  simp only [LinearMap.comp_apply] at this
  simp only [LinearMap.lcomp_apply', LinearMap.comp_apply, ModuleCat.hom_comp, this]
  simp

/-- The duals of the cycles of a totally acyclic complex have no higher extensions by `A`: the
dual sequences `0 ⟶ (Zᵏ⁺¹)* ⟶ (Pᵏ)* ⟶ (Zᵏ)* ⟶ 0` form a chain, and a functional on `(Zᵏ⁺¹)*` is
evaluation at some `z ∈ Zᵏ⁺¹`, the image of some `p ∈ Pᵏ`, so evaluation at `p` extends it. -/
private theorem ext_dual_cycles_eq_zero (n : ℕ) (m : ℤ)
    (e : Ext.{u} (ModuleCat.of Aᵐᵒᵖ (Module.Dual A (P.cycles m))) (ModuleCat.of Aᵐᵒᵖ A) (n + 1)) :
    e = 0 := by
  have hS (k : ℤ) := P.shortExact_mk_iCycles_toCycles k (k + 1) (by simp) (hP.acyclic (k + 1))
  -- The dual sequences, indexed so that the cokernel of the `k`-th is `(Z⁻ᵏ)*`.
  let D : ℤ → ShortComplex (ModuleCat.{u} Aᵐᵒᵖ) := fun k ↦
    (ShortComplex.mk (P.iCycles (-k)) (P.toCycles (-k) (-k + 1))
      (P.iCycles_toCycles _ _)).moduleCatOpDual
  have hD (k : ℤ) : (D k).ShortExact :=
    (hS (-k)).moduleCatOpDual (hP.exists_extend_iCycles (-k))
  have (k : ℤ) : Projective (D k).X₂ := by
    have := hP.finite (-k)
    have := hP.projective (-k)
    infer_instance
  refine ext_eq_zero_of_iso (eqToIso (by
      simp only [D, ShortComplex.moduleCatOpDual_X₃]
      rw [neg_neg]))
    (ext_X₃_eq_zero_of_forall_exists_f_comp_eq hD
      (fun k ↦ eqToIso (by
        simp only [D, ShortComplex.moduleCatOpDual_X₃, ShortComplex.moduleCatOpDual_X₁]
        rw [show -(k + 1) + 1 = -k by lia]))
      (fun k φ ↦ ?_) n (-m)) e
  obtain ⟨z, hz⟩ := (hP.bijective_opDualEval (-k + 1) (Iso.refl _)).2 φ.hom
  obtain ⟨p, rfl⟩ := (hS (-k)).moduleCat_surjective_g z
  refine ⟨ModuleCat.ofHom (opDualEval A (P.X (-k)) p), ?_⟩
  ext ψ
  rw [← hz]
  -- Rewriting with `ShortComplex.moduleCatOpDual_f` leaves objects of the dual short complex in
  -- the types of the composite, which blocks `ModuleCat.hom_comp`; state the composite as the
  -- linear map it is by definition instead.
  change opDualEval A (P.X (-k)) p ((P.toCycles (-k) (-k + 1)).hom.lcomp Aᵐᵒᵖ A ψ) = _
  rw [opDualEval_apply]
  exact (opDualEval_apply A _ _ ψ).symm

end CochainComplex.IsTotallyAcyclic

namespace TauCeti

variable {A : Type u} [Ring A]

/-- **Gorenstein-projective modules are totally reflexive**, over any ring. -/
theorem IsGorensteinProjective.isTotallyReflexive {M : ModuleCat.{u} A}
    (hM : IsGorensteinProjective A M) : IsTotallyReflexive A M := by
  obtain ⟨P, hP, ⟨i⟩⟩ := (isGorensteinProjective_iff M).1 hM
  refine ⟨hM.finite, hP.bijective_opDualEval 0 i.symm, fun n e ↦ hM.ext_eq_zero _ e,
    fun n e ↦ ?_⟩
  -- Transport along the dual `M* ≅ (Z⁰)*` of `Z⁰ ≅ M`.
  exact ext_eq_zero_of_iso (LinearEquiv.congrLeft A Aᵐᵒᵖ i.symm.toLinearEquiv).toModuleIso
    (hP.ext_dual_cycles_eq_zero n 0) e

end TauCeti

namespace TauCeti

variable {A : Type u} [Ring A]

variable (A) in
/-- The finitely generated modules `X` with `Ext^{n+1}(X, A) = 0` for all `n`. -/
private def extOrthogonal : ObjectProperty (ModuleCat.{u} A) := fun X ↦
  Module.Finite A X ∧ ∀ (n : ℕ) (e : Ext.{u} X (ModuleCat.of A A) (n + 1)), e = 0

/-- Over a left noetherian ring, a finitely generated module without higher extensions by `A` is
the last term of a sequence `0 ⟶ X' ⟶ Aⁿ ⟶ X ⟶ 0` with `X'` of the same kind. -/
private theorem exists_syzygy [IsNoetherianRing A] (X : ModuleCat.{u} A)
    (hX : extOrthogonal A X) : ∃ S : ShortComplex (ModuleCat.{u} A),
      S.IsCompleteResolutionStep ∧ extOrthogonal A S.X₁ ∧ Nonempty (S.X₃ ≅ X) := by
  have := hX.1
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A X
  let S := ModuleCat.shortComplexOfCompEqZero (LinearMap.ker π).subtype π (by ext; simp)
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (LinearMap.exact_subtype_ker_map π) Subtype.val_injective hπ
  have : Projective S.X₂ := inferInstanceAs (Projective (ModuleCat.of A (Fin n → A)))
  exact ⟨S, ⟨hS, inferInstanceAs (Module.Finite A (Fin n → A)), this,
    hS.moduleCat_exists_comp_eq_of_ext_eq_zero (hX.2 0)⟩,
    ⟨inferInstanceAs (Module.Finite A (LinearMap.ker π)),
      fun n ↦ ext_X₁_eq_zero_of_ext_X₃_eq_zero hS (hX.2 (n + 1))⟩, ⟨Iso.refl _⟩⟩

/-- Over a right noetherian ring, a totally reflexive module `M` is the first term of a sequence
`0 ⟶ M ⟶ Aᵏ ⟶ M' ⟶ 0` with `M'` totally reflexive: the map to `Aᵏ` is given by generators of
`M*`. -/
private theorem exists_cosyzygy [IsNoetherianRing Aᵐᵒᵖ] (M : ModuleCat.{u} A)
    (hM : IsTotallyReflexive A M) : ∃ S : ShortComplex (ModuleCat.{u} A),
      S.IsCompleteResolutionStep ∧ IsTotallyReflexive A S.X₃ ∧ Nonempty (S.X₁ ≅ M) := by
  have := hM.finite
  -- `M*` embeds in the dual of a finite free module, so it is finitely generated.
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' A M
  have : Module.Finite Aᵐᵒᵖ (Module.Dual A M) := Module.Finite.of_injective
    (π.lcomp Aᵐᵒᵖ A) (LinearMap.lcomp_injective_of_surjective π hπ)
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := Aᵐᵒᵖ) (M := Module.Dual A M)
  let j : M →ₗ[A] (Fin k → A) := LinearMap.pi s
  have hj : Function.Surjective (j.lcomp Aᵐᵒᵖ A) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨LinearMap.proj i, by ext; simp [j]⟩
  have hjinj : Function.Injective j := by
    refine (injective_iff_map_eq_zero _).2 fun m hm ↦ hM.bijective_opDualEval.1 ?_
    rw [map_zero]
    ext φ
    obtain ⟨ψ, rfl⟩ := hj φ
    simp [hm]
  let S := ModuleCat.shortComplexOfCompEqZero j (LinearMap.range j).mkQ (by ext; simp)
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (LinearMap.exact_map_mkQ_range j) hjinj (Submodule.mkQ_surjective _)
  have hproj : Projective S.X₂ := inferInstanceAs (Projective (ModuleCat.of A (Fin k → A)))
  have hD := hS.moduleCatOpDual hj
  refine ⟨S, ⟨hS, inferInstanceAs (Module.Finite A (Fin k → A)), hproj, hj⟩,
    ⟨inferInstanceAs (Module.Finite A ((Fin k → A) ⧸ LinearMap.range j)), ?_,
      fun n ↦ ?_, fun n ↦ ext_X₁_eq_zero_of_ext_X₃_eq_zero hD (hM.ext_dual_eq_zero (n + 1))⟩,
    ⟨Iso.refl _⟩⟩
  · -- Reflexivity of the cokernel; functionals on `M'*` extend to `(Aᵏ)*` as `Ext¹(M*, A) = 0`.
    refine opDualEval_bijective_of_exact_of_surjective A (LinearMap.exact_map_mkQ_range j)
      (Submodule.mkQ_surjective _) hj (fun χ ↦ ?_) hM.bijective_opDualEval.2
      (opDualEval_bijective A _)
    exact hD.moduleCat_exists_comp_eq_of_ext_eq_zero (hM.ext_dual_eq_zero 0) χ
  · -- `Ext^{n+1}(M', A) = 0` by dimension shifting, as functionals on `M` extend to `Aᵏ`.
    cases n with
    | zero => exact hS.moduleCat_ext_eq_zero_of_exists_comp_eq hj
    | succ n => exact ext_X₃_eq_zero_of_ext_X₁_eq_zero hS (hM.ext_eq_zero n)

/-- **Totally reflexive modules are Gorenstein-projective** over a left and right noetherian
ring. -/
theorem IsTotallyReflexive.isGorensteinProjective [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    {M : ModuleCat.{u} A} (hM : IsTotallyReflexive A M) : IsGorensteinProjective A M :=
  isGorensteinProjective_of_isCompleteResolutionStep (extOrthogonal A) (IsTotallyReflexive A)
    (fun _ hX ↦ ⟨hX.finite, hX.ext_eq_zero⟩) exists_syzygy exists_cosyzygy hM

/-- **Auslander–Bridger**: over a left and right noetherian ring, a module is totally reflexive if
and only if it is Gorenstein-projective. -/
theorem isTotallyReflexive_iff_isGorensteinProjective [IsNoetherianRing A]
    [IsNoetherianRing Aᵐᵒᵖ] (M : ModuleCat.{u} A) :
    IsTotallyReflexive A M ↔ IsGorensteinProjective A M :=
  ⟨IsTotallyReflexive.isGorensteinProjective, IsGorensteinProjective.isTotallyReflexive⟩

end TauCeti
