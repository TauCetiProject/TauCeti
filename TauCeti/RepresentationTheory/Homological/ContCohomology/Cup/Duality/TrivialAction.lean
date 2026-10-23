/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.FourLemma

import Mathlib.Data.FunLike.Fintype
import Mathlib.Topology.Algebra.Group.Quotient
import TauCeti.Algebra.Module.ZMod.Dual
import TauCeti.Algebra.Module.ZMod.Injective

/-!
# Tate's duality maps on modules with trivial action

Let `G` be a topological group and `N` a discrete `G`-module on which `G` acts trivially, with
`N ≃+ ZMod n` and `H²(G, N) ≃+ ZMod n` for some `n ≠ 0`. For a finite discrete `G`-module `A`
write `A' = InternalHom G A N` for its dual and `αᵢ : Hⁱ(G, A) → Hom(H²⁻ⁱ(G, A'), H²(G, N))`,
`i = 0, 1, 2`, for Tate's duality maps (`TauCeti.ContCohomology.dualityMap0`, `dualityMap1`,
`dualityMap2`).

This file proves that **Tate's duality for the module `N` itself gives Tate's duality for every
finite module killed by `n` with trivial action**
(`TauCeti.ContCohomology.dualityMap0_bijective_of_smul_eq_self`,
`dualityMap1_bijective_of_smul_eq_self`, `dualityMap2_bijective_of_smul_eq_self`): if `α₀`, `α₁`
are bijective and `α₂` is injective for `A = N`, and `H¹(G, N)` is finite, then the three duality
maps are bijective for every such `A`. Over a local field `K` containing the `n`-th roots of
unity, with `N = ℤ/n ≅ μₙ`, this is the passage from the cyclic module `ℤ/n` to every finite
module on which the Galois group acts trivially, the base case of local Tate duality.

A finite module with trivial action need not be a sum of copies of `N` (`ℤ/2` is not a direct
summand of `ℤ/4`), so the argument runs through the free modules `Nᵏ = Fin k → N` and the
injectivity statements, which then upgrade to bijectivity by counting.

* **Free modules.** Along the split sequence `0 → N → Nᵏ⁺¹ → Nᵏ → 0`, the four lemmas
  (`TauCeti.ContCohomology.DiscreteShortExact.dualityMap0_surjective` and its companions) carry
  `α₀` surjective, `α₁` bijective and `α₂` injective from `N` to every `Nᵏ`.
* **Degree zero.** `α₀` is injective on every finite `A` with trivial action killed by `n`, because
  the maps `A → N` separate the points of `A` (`TauCeti.exists_addMonoidHom_zmod_apply_ne_zero`)
  and `α₀` is natural in the module
  (`TauCeti.ContCohomology.dualityMap0_explicitCoeff0`).
* **Degrees one and two.** The same maps embed `A` into a free module `Nᵏ`, whose cokernel `C` is
  again finite with trivial action and killed by `n`. The four lemmas concluding injectivity on
  the submodule (`TauCeti.ContCohomology.DiscreteShortExact.dualityMap1_injective_left`,
  `DiscreteShortExact.dualityMap2_injective_left`) along `0 → A → Nᵏ → C → 0` then give `α₁`
  injective on `A` from `α₀` injective on `C`, and `α₂` injective on `A` from `α₁` injective on
  `C`.
* **Counting.** The dual `A'` is again finite with trivial action and killed by `n`, and `H¹(G, A')`
  is finite, embedding into a power of `H¹(G, N)`
  (`TauCeti.ContCohomology.finite_H1_of_smul_eq_self`); so injectivity of `αᵢ` on `A` and of
  `α₂₋ᵢ` on `A'` makes `αᵢ` bijective on `A`
  (`TauCeti.ContCohomology.dualityMap0_bijective_of_injective_of_addEquiv_zmod` and its
  companions).

## Main results

* `TauCeti.ContCohomology.finite_H1_of_smul_eq_self`: for trivial actions, `H¹(G, A)` is finite
  for every finite `A` killed by `n` once `H¹(G, N)` is.
* `TauCeti.ContCohomology.dualityMap0_injective_of_smul_eq_self`: `α₀` is injective on every
  finite `A` with trivial action killed by `n` once it is injective on `N`.
* `TauCeti.ContCohomology.dualityMap0_bijective_of_smul_eq_self`,
  `dualityMap1_bijective_of_smul_eq_self` and `dualityMap2_bijective_of_smul_eq_self`: Tate's
  duality on every finite module with trivial action killed by `n`, from Tate's duality on `N`.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. II, §5.2, proof of Theorem 2.
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, proof of Theorem 2.1.
-/

public section

namespace TauCeti.ContCohomology

universe uG uN uA

variable {G : Type uG} [Group G] {N : Type uN} [AddCommGroup N] [DistribMulAction G N] {n : ℕ}
  [NeZero n] (hN : ∀ (g : G) (y : N), g • y = y) (e : N ≃+ ZMod n)

section Separation

variable {A : Type uA} [AddCommGroup A] [DistribMulAction G A] (hA : ∀ a : A, n • a = 0)
  (hAtriv : ∀ (g : G) (a : A), g • a = a)

include hN e hA hAtriv

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace N] [DiscreteTopology N]
  [ContinuousSMul G N] [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul G A]

omit [IsTopologicalGroup G] in
/-- **`H¹` of a module with trivial action is finite** when `H¹(G, N)` is: for a finite `A` killed
by `n` on which `G` acts trivially, the classes of `H¹(G, A)` are continuous homomorphisms
`G → A`, and the maps `A → N` separate them, so `H¹(G, A)` embeds into a finite power of
`H¹(G, N)`. -/
theorem finite_H1_of_smul_eq_self [Finite A] [Finite (H1 G N)] : Finite (H1 G A) := by
  have : Finite N := Finite.of_equiv _ e.symm.toEquiv
  have : Finite (A →+[G] N) := DFunLike.finite _
  refine Finite.of_injective (fun x (f : A →+[G] N) ↦
    explicitCoeff1 G A f continuous_of_discreteTopology x) fun x y hxy ↦ ?_
  induction x using QuotientAddGroup.induction_on with | H c => ?_
  induction y using QuotientAddGroup.induction_on with | H d => ?_
  -- the two cocycles agree after every map `A → N`, so they agree
  have hcd (f : A →+[G] N) (g : G) : f ((c : G → A) g) = f ((d : G → A) g) := by
    have h := congrArg (H1EquivOfSmulEqSelf hN) (congrFun hxy f)
    simp only [explicitCoeff1_mk, H1EquivOfSmulEqSelf_mk] at h
    have h' := congrFun (congrArg Subtype.val ((Z1EquivOfSmulEqSelf hN).injective h)) g
    exact (cocyclesMap1_apply G A G N _ _ _ _ c g).symm.trans
      (h'.trans (cocyclesMap1_apply G A G N _ _ _ _ d g))
  refine congrArg _ (Subtype.ext (funext fun g ↦ sub_eq_zero.1 (by_contra fun hne ↦ ?_)))
  obtain ⟨f, hf⟩ := exists_distribMulActionHom_apply_ne_zero hN e hA hAtriv hne
  exact hf (by rw [map_sub, hcd f g, sub_self])

/-- **`α₀` is injective on every module with trivial action killed by `n`** once it is injective
on `N`: an invariant `a ≠ 0` has a nonzero image under some map `f : A → N`, and
`α₀ (f a) = α₀ a ∘ f^*` by naturality. -/
theorem dualityMap0_injective_of_smul_eq_self [Finite A]
    (h₀ : haveI : Finite N := Finite.of_equiv _ e.symm.toEquiv
      Function.Injective (dualityMap0 G N N)) :
    Function.Injective (dualityMap0 G A N) := by
  have : Finite N := Finite.of_equiv _ e.symm.toEquiv
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ Subtype.ext (by_contra fun hne ↦ ?_)
  obtain ⟨f, hf⟩ := exists_distribMulActionHom_apply_ne_zero hN e hA hAtriv hne
  have hfx : explicitCoeff0 G A f x = 0 := h₀ <| AddMonoidHom.ext fun b ↦ by
    rw [dualityMap0_explicitCoeff0, hx, map_zero, AddMonoidHom.zero_apply,
      AddMonoidHom.zero_apply]
  exact hf (by simpa using congrArg Subtype.val hfx)

end Separation

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace N] [DiscreteTopology N]
  [ContinuousSMul G N]

section FreeModules

/-! ### The free modules `Nᵏ` -/

/-- The split short exact sequence `0 → N → Nᵏ⁺¹ → Nᵏ → 0`, inclusion in the first coordinate
and projection onto the others. -/
private def piSuccShortExact (k : ℕ) : DiscreteShortExact G N (Fin (k + 1) → N) (Fin k → N) where
  incl := AddMonoidHom.single (fun _ : Fin (k + 1) ↦ N) 0
  proj := AddMonoidHom.pi fun i ↦ Pi.evalAddMonoidHom _ i.succ
  incl_equivariant g y := by
    simp only [hN, Pi.smul_def]
  proj_equivariant g f := by simp only [hN, Pi.smul_def]
  incl_injective _ _ h := Pi.single_injective (M := fun _ : Fin (k + 1) ↦ N) 0 h
  proj_surjective f := ⟨Fin.cons 0 f, funext fun i ↦ by simp⟩
  exact f := by
    refine ⟨fun h ↦ ⟨f 0, funext fun i ↦ ?_⟩, ?_⟩
    · refine Fin.cases (by simp) (fun i ↦ ?_) i
      simpa [Fin.succ_ne_zero] using (congrFun h i).symm
    · rintro ⟨y, rfl⟩
      exact funext fun i ↦ by simp [Fin.succ_ne_zero]

variable (e₂ : H2 G N ≃+ ZMod n)

include hN e e₂

/-- On the free modules `Nᵏ`, `α₀` is surjective, `α₁` bijective and `α₂` injective, by induction
on `k` along `0 → N → Nᵏ⁺¹ → Nᵏ → 0` and the four lemmas. -/
private theorem dualityMap_pi [Finite N] (h₀ : Function.Surjective (dualityMap0 G N N))
    (h₁ : Function.Bijective (dualityMap1 G N N)) (h₂ : Function.Injective (dualityMap2 G N N))
    (k : ℕ) : Function.Surjective (dualityMap0 G (Fin k → N) N) ∧
      Function.Bijective (dualityMap1 G (Fin k → N) N) ∧
        Function.Injective (dualityMap2 G (Fin k → N) N) := by
  induction k with
  | zero =>
    -- the zero module: both sides of each duality map are trivial
    exact ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩,
      ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩,
      fun _ _ _ ↦ Subsingleton.elim _ _⟩
  | succ k ih =>
    obtain ⟨_, hNB⟩ := Module.Baer.exists_module_of_addEquiv_zmod e
    obtain ⟨_, hH2⟩ := Module.Baer.exists_module_of_addEquiv_zmod e₂
    let S := piSuccShortExact hN k
    have hB (f : Fin (k + 1) → N) : n • f = 0 := funext fun i ↦ e.injective (by simp)
    have hsurj := S.precomp_inclDistribMulActionHom_surjective_of_baer N hNB hB
    exact ⟨S.dualityMap0_surjective hsurj hB hH2 h₀ ih.1 h₁.1,
      ⟨S.dualityMap1_injective hsurj hB hH2 ih.1 h₁.1 ih.2.1.1,
        S.dualityMap1_surjective hsurj hB hH2 h₁.2 ih.2.1.2 h₂⟩,
      S.dualityMap2_injective hsurj hB hH2 ih.2.1.2 h₂ ih.2.2⟩

end FreeModules

section Embedding

variable {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A] [Finite A] (hA : ∀ a : A, n • a = 0)
  (hAtriv : ∀ (g : G) (a : A), g • a = a)

include hN e hA hAtriv

omit [IsTopologicalGroup G] [ContinuousSMul G N] [ContinuousSMul G A] in
/-- A finite module `A` with trivial action killed by `n` embeds into a free module `Nᵏ`, with a
cokernel that is again finite with trivial action and killed by `n`. The embedding is given by
all maps `A → N`, which separate the points of `A`. -/
private theorem exists_discreteShortExact : ∃ (k : ℕ) (C : Type uN) (_ : AddCommGroup C)
    (_ : TopologicalSpace C) (_ : DiscreteTopology C) (_ : DistribMulAction G C)
    (_ : ContinuousSMul G C) (_ : Finite C), (∀ (g : G) (c : C), g • c = c) ∧
      (∀ c : C, n • c = 0) ∧ Nonempty (DiscreteShortExact G A (Fin k → N) C) := by
  have : Finite N := Finite.of_equiv _ e.symm.toEquiv
  have : Finite (A →+[G] N) := DFunLike.finite _
  let eA := Finite.equivFin (A →+[G] N)
  let ι : A →+ (Fin (Nat.card (A →+[G] N)) → N) := AddMonoidHom.pi fun i ↦ (eA.symm i : A →+ N)
  have hι : Function.Injective ι := (injective_iff_map_eq_zero _).2 fun a ha ↦ by
    by_contra hne
    obtain ⟨f, hf⟩ := exists_distribMulActionHom_apply_ne_zero hN e hA hAtriv hne
    exact hf (by simpa [ι] using congrFun ha (eA f))
  let C := (Fin (Nat.card (A →+[G] N)) → N) ⧸ ι.range
  let _ : DistribMulAction G C :=
    { smul _ c := c
      one_smul _ := rfl
      mul_smul _ _ _ := rfl
      smul_zero _ := rfl
      smul_add _ _ _ := rfl }
  have hCtriv (g : G) (c : C) : g • c = c := rfl
  refine ⟨_, C, inferInstance, inferInstance,
    QuotientAddGroup.discreteTopology (isOpen_discrete _), inferInstance,
    ⟨continuous_snd.congr fun x ↦ (hCtriv x.1 x.2).symm⟩,
    Finite.of_surjective _ (QuotientAddGroup.mk'_surjective _), hCtriv, fun c ↦ ?_,
    ⟨{ incl := ι
       proj := QuotientAddGroup.mk' _
       incl_equivariant g a := by simp only [hAtriv, hN, Pi.smul_def]
       proj_equivariant g f := by simp only [hN, hCtriv, Pi.smul_def]
       incl_injective := hι
       proj_surjective := QuotientAddGroup.mk'_surjective _
       exact f := (QuotientAddGroup.eq_zero_iff f).trans AddMonoidHom.mem_range }⟩⟩
  induction c using QuotientAddGroup.induction_on with | H f => ?_
  have hf : n • f = 0 := funext fun i ↦ e.injective (by simp)
  rw [← QuotientAddGroup.mk_nsmul, hf, QuotientAddGroup.mk_zero]

end Embedding

section Injective

variable (e₂ : H2 G N ≃+ ZMod n)
  (h₀ : haveI : Finite N := Finite.of_equiv _ e.symm.toEquiv
    Function.Bijective (dualityMap0 G N N))
  (h₁ : haveI : Finite N := Finite.of_equiv _ e.symm.toEquiv
    Function.Bijective (dualityMap1 G N N))
  (h₂ : haveI : Finite N := Finite.of_equiv _ e.symm.toEquiv
    Function.Injective (dualityMap2 G N N))
  {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A] [Finite A] (hA : ∀ a : A, n • a = 0)
  (hAtriv : ∀ (g : G) (a : A), g • a = a)

include hN e e₂ h₀ h₁ h₂ hA hAtriv

/-- `α₁` is injective on every finite module with trivial action killed by `n`, by the four lemma
along an embedding `0 → A → Nᵏ → C → 0`, using `α₀` injective on the cokernel `C`. -/
private theorem dualityMap1_injective_of_smul_eq_self :
    Function.Injective (dualityMap1 G A N) := by
  have : Finite N := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨k, C, _, _, _, _, _, _, hCtriv, hC, ⟨S⟩⟩ := exists_discreteShortExact hN e hA hAtriv
  obtain ⟨_, hNB⟩ := Module.Baer.exists_module_of_addEquiv_zmod e
  obtain ⟨_, hH2⟩ := Module.Baer.exists_module_of_addEquiv_zmod e₂
  have hB (f : Fin k → N) : n • f = 0 := funext fun i ↦ e.injective (by simp)
  have hF := dualityMap_pi hN e e₂ h₀.2 h₁ h₂ k
  exact S.dualityMap1_injective_left (S.precomp_inclDistribMulActionHom_surjective_of_baer N hNB hB)
    hB hH2 hF.1 (dualityMap0_injective_of_smul_eq_self hN e hC hCtriv h₀.1) hF.2.1.1

/-- `α₂` is injective on every finite module with trivial action killed by `n`, by the four lemma
along an embedding `0 → A → Nᵏ → C → 0`, using `α₁` injective on the cokernel `C`. -/
private theorem dualityMap2_injective_of_smul_eq_self :
    Function.Injective (dualityMap2 G A N) := by
  have : Finite N := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨k, C, _, _, _, _, _, _, hCtriv, hC, ⟨S⟩⟩ := exists_discreteShortExact hN e hA hAtriv
  obtain ⟨_, hNB⟩ := Module.Baer.exists_module_of_addEquiv_zmod e
  obtain ⟨_, hH2⟩ := Module.Baer.exists_module_of_addEquiv_zmod e₂
  have hB (f : Fin k → N) : n • f = 0 := funext fun i ↦ e.injective (by simp)
  have hF := dualityMap_pi hN e e₂ h₀.2 h₁ h₂ k
  exact S.dualityMap2_injective_left (S.precomp_inclDistribMulActionHom_surjective_of_baer N hNB hB)
    hB hH2 hF.2.1.2 (dualityMap1_injective_of_smul_eq_self hN e e₂ h₀ h₁ h₂ hC hCtriv) hF.2.2

end Injective

section Bijective

/-! ### Bijectivity, by counting -/

variable (e₂ : H2 G N ≃+ ZMod n)
  (h₀ : haveI : Finite N := Finite.of_equiv _ e.symm.toEquiv
    Function.Bijective (dualityMap0 G N N))
  (h₁ : haveI : Finite N := Finite.of_equiv _ e.symm.toEquiv
    Function.Bijective (dualityMap1 G N N))
  (h₂ : haveI : Finite N := Finite.of_equiv _ e.symm.toEquiv
    Function.Injective (dualityMap2 G N N))
  (A : Type uA) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A] [Finite A] (hA : ∀ a : A, n • a = 0)
  (hAtriv : ∀ (g : G) (a : A), g • a = a)

include hN e e₂ h₀ h₁ h₂ hA hAtriv

/-- **Tate's duality map `α₀` on a module with trivial action.** Let `N` be a discrete `G`-module
with trivial action, `N ≃+ ZMod n` and `H²(G, N) ≃+ ZMod n`, on which `α₀`, `α₁` are bijective and
`α₂` is injective. Then `α₀ : H⁰(G, A) → Hom(H²(G, A'), H²(G, N))` is bijective for every finite
discrete `G`-module `A` killed by `n` on which `G` acts trivially. -/
theorem dualityMap0_bijective_of_smul_eq_self : Function.Bijective (dualityMap0 G A N) := by
  have : Finite N := Finite.of_equiv _ e.symm.toEquiv
  have hA' := InternalHom.nsmul_eq_zero_of_domain (G := G) (N := N) hA
  exact dualityMap0_bijective_of_injective_of_addEquiv_zmod e e₂ hA
    (dualityMap2_injective_of_smul_eq_self hN e e₂ h₀ h₁ h₂ hA'
      (InternalHom.smul_eq_self_of_smul_eq_self hAtriv hN))
    (dualityMap0_injective_of_smul_eq_self hN e hA hAtriv h₀.1)

/-- **Tate's duality map `α₁` on a module with trivial action.** Under the hypotheses of
`TauCeti.ContCohomology.dualityMap0_bijective_of_smul_eq_self`, if moreover `H¹(G, N)` is finite,
then `α₁ : H¹(G, A) → Hom(H¹(G, A'), H²(G, N))` is bijective for every finite discrete `G`-module
`A` killed by `n` on which `G` acts trivially. -/
theorem dualityMap1_bijective_of_smul_eq_self [Finite (H1 G N)] :
    Function.Bijective (dualityMap1 G A N) := by
  have : Finite N := Finite.of_equiv _ e.symm.toEquiv
  have hA' := InternalHom.nsmul_eq_zero_of_domain (G := G) (N := N) hA
  have hA'triv := InternalHom.smul_eq_self_of_smul_eq_self hAtriv hN
  have : Finite (H1 G (InternalHom G A N)) := finite_H1_of_smul_eq_self hN e hA' hA'triv
  exact dualityMap1_bijective_of_injective_of_addEquiv_zmod e e₂ hA
    (dualityMap1_injective_of_smul_eq_self hN e e₂ h₀ h₁ h₂ hA' hA'triv)
    (dualityMap1_injective_of_smul_eq_self hN e e₂ h₀ h₁ h₂ hA hAtriv)

/-- **Tate's duality map `α₂` on a module with trivial action.** Under the hypotheses of
`TauCeti.ContCohomology.dualityMap0_bijective_of_smul_eq_self`,
`α₂ : H²(G, A) → Hom(H⁰(G, A'), H²(G, N))` is bijective for every finite discrete `G`-module `A`
killed by `n` on which `G` acts trivially. -/
theorem dualityMap2_bijective_of_smul_eq_self : Function.Bijective (dualityMap2 G A N) := by
  have : Finite N := Finite.of_equiv _ e.symm.toEquiv
  have hA' := InternalHom.nsmul_eq_zero_of_domain (G := G) (N := N) hA
  exact dualityMap2_bijective_of_injective_of_addEquiv_zmod e e₂ hA
    (dualityMap0_injective_of_smul_eq_self hN e hA'
      (InternalHom.smul_eq_self_of_smul_eq_self hAtriv hN) h₀.1)
    (dualityMap2_injective_of_smul_eq_self hN e e₂ h₀ h₁ h₂ hA hAtriv)

end Bijective

end TauCeti.ContCohomology
