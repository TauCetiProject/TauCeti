/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.TraceShortExact
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.FourLemma
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Cup
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.CupForm
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.FiniteCoefficients
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Coeffaceable
public import TauCeti.Topology.Algebra.GroupAction.InternalHom.DoubleDual

/-!
# Tate's duality maps of a Demushkin group

For a finite discrete `𝔽_p[G]`-module `M` of a pro-`p` group `G`, Tate's duality maps
`αᵢ : Hⁱ(G, M) → Hom(H²⁻ⁱ(G, M'), H²(G, 𝔽_p))`, with `M' = Hom(M, 𝔽_p)`, are the cup products
with the evaluation pairing (`TauCeti.ContCohomology.dualityMap0`, `dualityMap1`, `dualityMap2`).
For an infinite Demushkin group they are isomorphisms for every such `M`: this is the perfect
duality on its finite modules, and the source of `cd_p G = 2`. This file proves it, following
Tate's argument in Serre's exposé, §9.1.

The base case is the trivial module `M = 𝔽_p`. Under evaluation at `1` the dual module
`Hom(𝔽_p, 𝔽_p)` is `𝔽_p` again, and the three maps read as follows. `α₁` is the cup square
`H¹(G, 𝔽_p) → Hom(H¹(G, 𝔽_p), H²(G, 𝔽_p))`, bijective because the cup square of a Demushkin group
is a perfect pairing (`TauCeti.IsDemushkin.cupFp_bijective`). `α₀` sends `c ∈ 𝔽_p = H⁰(G, 𝔽_p)` to
multiplication by `c` on `H²(G, 𝔽_p)`, bijective because `H²(G, 𝔽_p)` is one-dimensional. `α₂`
sends a class `b ∈ H²(G, 𝔽_p)` to `c ↦ c • b`, which is bijective for every group acting trivially
(`TauCeti.ContCohomology.dualityMap2_zmod_bijective`), so no statement about it is specific to
Demushkin groups.

The dévissage is the induction on the order of `M` of `TauCeti.IsProP.finite_pPrimary_induction`:
every finite `𝔽_p[G]`-module of a pro-`p` group is an iterated extension of trivial modules of
order `p`, and the four lemmas along a short exact sequence
(`TauCeti/RepresentationTheory/Homological/ContCohomology/Cup/Duality/FourLemma.lean`) carry
surjectivity of `α₀`, bijectivity of `α₁` and injectivity of `α₂` from the two ends of an
extension to its middle. Two further arguments, both needing `G` infinite, complete the duality.
Injectivity of `α₀` on `M` follows from injectivity of `α₁` on the kernel of a trace
`Coind_V^G M → M` that vanishes on invariants, which exists because `H⁰` is co-effaceable on an
infinite pro-`p` group (`TauCeti.IsProP.exists_isOpen_trace_eq_zero_of_mem_H0`). Surjectivity of
`α₂` on `M` is then a count: `H²(G, M)` is finite, and bijectivity of `α₀` on `M'` together with
the double duality `M ≅ M''` give `|H²(G, M)| = |H⁰(G, M')|`.

## Main results

* `TauCeti.IsDemushkin.explicitCup11_mul_bijective`: on the explicit models, the cup product of
  multiplication on `H¹(G, 𝔽_p)` is a perfect pairing.
* `TauCeti.IsDemushkin.dualityMap1_zmod_bijective`,
  `TauCeti.IsDemushkin.dualityMap0_zmod_bijective`: Tate's duality maps `α₁` and `α₀` at `M = 𝔽_p`
  are bijective.
* `TauCeti.IsDemushkin.dualityMap0_surjective`, `TauCeti.IsDemushkin.dualityMap1_bijective`,
  `TauCeti.IsDemushkin.dualityMap2_injective`: the dévissage, on every finite `𝔽_p[G]`-module `M`,
  `α₀` is surjective, `α₁` is bijective and `α₂` is injective.
* `TauCeti.IsDemushkin.dualityMap0_bijective`, `TauCeti.IsDemushkin.dualityMap2_bijective`: for an
  infinite Demushkin group all three duality maps are bijective on every finite `𝔽_p[G]`-module,
  **Tate's perfect duality**.

## References

* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki
  exp. 252 (1963), §9.1.
-/

public section

namespace TauCeti

open TauCeti.ContCohomology

universe u

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the explicit
-- `H²(G, 𝔽_p)` below is the one `TauCeti.cohomFpAddEquivH2` is stated against.
attribute [local instance 2000] Ring.toAddCommGroup

namespace IsDemushkin

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] (hG : IsDemushkin p G) [DistribMulAction G (ZMod p)]
  [ContinuousSMul G (ZMod p)] (htriv : ∀ (g : G) (m : ZMod p), g • m = m)

include hG htriv

/-- **The cup product of multiplication on the explicit `H¹(G, 𝔽_p)` is a perfect pairing**: for a
Demushkin group and any trivial action of `G` on `ZMod p`, `x ↦ (x ⌣ ·)` is a bijection from
`H1 G (ZMod p)` onto the additive homomorphisms `H1 G (ZMod p) →+ H2 G (ZMod p)`. This is
`TauCeti.IsDemushkin.cupFp_bijective` transported to the explicit models. -/
theorem explicitCup11_mul_bijective :
    Function.Bijective (explicitCup11 G (ZMod p) (ZMod p) (ZMod p) AddMonoidHom.mul continuous_mul
      (smul_mul_smul_of_smul_eq_self htriv)) := by
  have hcup : ∀ x y : H1 G (ZMod p),
      explicitCup11 G (ZMod p) (ZMod p) (ZMod p) AddMonoidHom.mul continuous_mul
        (smul_mul_smul_of_smul_eq_self htriv) x y =
      cohomFpAddEquivH2 p G htriv (cupFp p G ((cohomFpAddEquivH1 p G htriv).symm x)
        ((cohomFpAddEquivH1 p G htriv).symm y)) := fun x y => by
    rw [cupFp_cohomFpAddEquivH1_symm, AddEquiv.apply_symm_apply]
  constructor
  · intro x x' h
    apply (cohomFpAddEquivH1 p G htriv).symm.injective
    apply hG.cupFp_bijective.1
    ext y
    have := congrArg
      (fun f : H1 G (ZMod p) →+ H2 G (ZMod p) => f (cohomFpAddEquivH1 p G htriv y)) h
    simp only [hcup, AddEquiv.symm_apply_apply] at this
    exact (cohomFpAddEquivH2 p G htriv).injective this
  · intro f
    obtain ⟨a, ha⟩ := hG.cupFp_bijective.2
      (((cohomFpAddEquivH2 p G htriv).symm.toAddMonoidHom.comp
        (f.comp (cohomFpAddEquivH1 p G htriv).toAddMonoidHom)).toZModLinearMap p)
    refine ⟨cohomFpAddEquivH1 p G htriv a, AddMonoidHom.ext fun y => ?_⟩
    rw [hcup, AddEquiv.symm_apply_apply, ha]
    simp

/-- **Tate's duality map `α₁` of a Demushkin group is bijective at `M = 𝔽_p`**: for any trivial
action of `G` on `ZMod p`, `H¹(G, 𝔽_p) → Hom(H¹(G, Hom(𝔽_p, 𝔽_p)), H²(G, 𝔽_p))` is a bijection.
Under evaluation at `1` it is the cup square, a perfect pairing. -/
theorem dualityMap1_zmod_bijective : Function.Bijective (dualityMap1 G (ZMod p) (ZMod p)) := by
  have hΨ := hG.explicitCup11_mul_bijective htriv
  constructor
  · intro a a' h
    apply hΨ.1
    refine AddMonoidHom.ext fun y => ?_
    have := congrArg (fun f : H1 G (InternalHom G (ZMod p) (ZMod p)) →+ H2 G (ZMod p) =>
      f ((H1InternalHomZModEquiv htriv).symm y)) h
    simpa only [dualityMap1_zmod htriv, AddEquiv.apply_symm_apply] using this
  · intro f
    obtain ⟨a, ha⟩ := hΨ.2 (f.comp (H1InternalHomZModEquiv htriv).symm.toAddMonoidHom)
    refine ⟨a, AddMonoidHom.ext fun b => ?_⟩
    rw [dualityMap1_zmod htriv, ha]
    simp

/-- **Tate's duality map `α₀` of a Demushkin group is bijective at `M = 𝔽_p`**: for any trivial
action of `G` on `ZMod p`, `H⁰(G, 𝔽_p) → Hom(H²(G, Hom(𝔽_p, 𝔽_p)), H²(G, 𝔽_p))` is a bijection,
since `H²(G, 𝔽_p)` is one-dimensional. -/
theorem dualityMap0_zmod_bijective : Function.Bijective (dualityMap0 G (ZMod p) (ZMod p)) :=
  dualityMap0_zmod_bijective_of_finrank_eq_one htriv
    ((cohomFpLinearEquivH2 p G htriv).finrank_eq.symm.trans hG.finrank_cohomFp_two)

/-! ### Dévissage: the duality maps on every finite `𝔽_p[G]`-module -/

/-- **The dévissage of Tate's duality argument.** On every finite discrete `G`-module `M` killed
by `p`, `α₀` is surjective, `α₁` is bijective and `α₂` is injective: this holds on the trivial
modules of order `p`, which are `𝔽_p`, and passes through extensions by the four lemmas. -/
private theorem dualityMap_devissage (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
    (hM : ∀ x : M, p • x = 0) :
    Function.Surjective (dualityMap0 G M (ZMod p)) ∧
      Function.Bijective (dualityMap1 G M (ZMod p)) ∧
        Function.Injective (dualityMap2 G M (ZMod p)) := by
  -- The motive quantifies over finiteness, which the duality maps need to be stated and which the
  -- induction principle does not carry in its zero case.
  refine hG.isProP.finite_pPrimary_induction
    (motive := fun M _ _ _ _ _ ↦ ∀ [Finite M], (∀ x : M, p • x = 0) →
      Function.Surjective (dualityMap0 G M (ZMod p)) ∧
        Function.Bijective (dualityMap1 G M (ZMod p)) ∧
          Function.Injective (dualityMap2 G M (ZMod p)))
    (fun M _ _ _ _ _ _ _ _ ↦ ?_) (fun A _ _ _ _ _ _ hA htrivA _ _ ↦ ?_)
    (fun A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S _ _ _ _ _ hA hC _ hB ↦ ?_) M
    (isPPrimaryTorsion_iff.2 fun m ↦ ⟨1, by rw [pow_one, hM]⟩) hM
  · -- the zero module: both sides of each duality map are trivial
    exact ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩,
      ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩,
      fun _ _ _ ↦ Subsingleton.elim _ _⟩
  · -- a trivial module of order `p` is `𝔽_p`, where the three maps are bijective
    have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    obtain ⟨a, ha⟩ := (isAddCyclic_of_prime_card hA).exists_generator
    let e₀ : A ≃+ ZMod p := (zmodAddEquivOfGenerator ha hA).symm
    let e : A →+[G] ZMod p :=
      { e₀.toAddMonoidHom with
        map_smul' := fun g a ↦ by rw [MonoidHom.id_apply, htrivA g a, htriv g] }
    have he : Function.Bijective e := e₀.bijective
    exact ⟨(dualityMap0_bijective_of_bijective he (hG.dualityMap0_zmod_bijective htriv)).2,
      dualityMap1_bijective_of_bijective he (hG.dualityMap1_zmod_bijective htriv),
      (dualityMap2_bijective_of_bijective he (dualityMap2_zmod_bijective htriv)).1⟩
  · -- the extension step: the four lemmas along `0 → A → B → C → 0`
    obtain ⟨h₀A, h₁A, h₂A⟩ := hA (S.nsmul_eq_zero_left hB)
    obtain ⟨h₀C, h₁C, h₂C⟩ := hC (S.nsmul_eq_zero_right hB)
    exact ⟨S.dualityMap0_surjective hB h₀A h₀C h₁A.1,
      ⟨S.dualityMap1_injective hB h₀C h₁A.1 h₁C.1, S.dualityMap1_surjective hB h₁A.2 h₁C.2 h₂A⟩,
      S.dualityMap2_injective hB h₁C.2 h₂A h₂C⟩

variable (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M] [Finite M] (hM : ∀ x : M, p • x = 0)
include hM

/-- **Tate's duality map `α₀` of a Demushkin group is surjective** on every finite discrete
`G`-module `M` killed by `p`. -/
theorem dualityMap0_surjective : Function.Surjective (dualityMap0 G M (ZMod p)) :=
  (hG.dualityMap_devissage htriv M hM).1

/-- **Tate's duality map `α₁` of a Demushkin group is bijective** on every finite discrete
`G`-module `M` killed by `p`: `H¹(G, M) × H¹(G, M') → H²(G, 𝔽_p)` is a perfect pairing. -/
theorem dualityMap1_bijective : Function.Bijective (dualityMap1 G M (ZMod p)) :=
  (hG.dualityMap_devissage htriv M hM).2.1

/-- **Tate's duality map `α₂` of a Demushkin group is injective** on every finite discrete
`G`-module `M` killed by `p`. -/
theorem dualityMap2_injective : Function.Injective (dualityMap2 G M (ZMod p)) :=
  (hG.dualityMap_devissage htriv M hM).2.2

end IsDemushkin

/-! ### Perfect duality for infinite Demushkin groups -/

namespace IsDemushkin

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] [Infinite G] (hG : IsDemushkin p G)
  [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)]
  (htriv : ∀ (g : G) (m : ZMod p), g • m = m)
  (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M] [Finite M] (hM : ∀ x : M, p • x = 0)

include hG htriv hM

/-- **Tate's duality map `α₀` of an infinite Demushkin group is injective** on every finite
discrete `G`-module `M` killed by `p`. The trace `Coind_V^G M → M` along a deep enough open
subgroup `V` vanishes on invariants, and `α₁` is injective on its kernel. -/
theorem dualityMap0_injective : Function.Injective (dualityMap0 G M (ZMod p)) := by
  obtain ⟨V, _, hV, htr⟩ := hG.isProP.exists_isOpen_trace_eq_zero_of_mem_H0 M
    (isPPrimaryTorsion_iff.2 fun m ↦ ⟨1, by rw [pow_one, hM]⟩)
  have hcoind : ∀ f : DiscreteCoind G V M, p • f = 0 := DiscreteCoind.nsmul_eq_zero hM
  refine (DiscreteCoind.traceShortExact G V M hV).dualityMap0_injective_of_explicitCoeff0_eq_zero
    hcoind ?_ (hG.dualityMap1_bijective htriv (DiscreteCoind.traceKer G V M)
      fun f ↦ Subtype.ext (by simpa using hcoind f)).1
  refine AddMonoidHom.ext fun f ↦ Subtype.ext ?_
  rw [coe_explicitCoeff0, AddMonoidHom.zero_apply, DiscreteShortExact.projDistribMulActionHom_apply,
    DiscreteCoind.traceShortExact_proj]
  exact htr f f.2

/-- **Tate's duality map `α₀` of an infinite Demushkin group is bijective** on every finite
discrete `G`-module `M` killed by `p`: `H⁰(G, M) × H²(G, M') → H²(G, 𝔽_p)` is a perfect pairing. -/
theorem dualityMap0_bijective : Function.Bijective (dualityMap0 G M (ZMod p)) :=
  ⟨hG.dualityMap0_injective htriv M hM, hG.dualityMap0_surjective htriv M hM⟩

omit [TotallyDisconnectedSpace G] [Infinite G] hM in
/-- The explicit `H²(G, 𝔽_p)` of a Demushkin group has `p` elements. -/
private theorem natCard_H2_zmod : Nat.card (H2 G (ZMod p)) = p := by
  have : Module.Finite (ZMod p) (cohomFp p G 2) :=
    Module.finite_of_finrank_eq_succ hG.finrank_cohomFp_two
  rw [← Nat.card_congr (cohomFpAddEquivH2 p G htriv).toEquiv,
    Module.natCard_eq_pow_finrank (K := ZMod p), hG.finrank_cohomFp_two, pow_one, Nat.card_zmod]

omit [TotallyDisconnectedSpace G] [Infinite G] hM in
/-- **Homomorphisms into `H²(G, 𝔽_p)` of a Demushkin group are as many as their source**: for a
finite abelian group `V` killed by `p`, `|Hom(V, H²(G, 𝔽_p))| = |V|`, since `H²(G, 𝔽_p)` is
one-dimensional over `𝔽_p`. -/
theorem natCard_addMonoidHom_H2 (V : Type*) [AddCommGroup V] [Finite V]
    (hV : ∀ v : V, p • v = 0) : Nat.card (V →+ H2 G (ZMod p)) = Nat.card V := by
  obtain ⟨a, ha⟩ :=
    (isAddCyclic_of_prime_card (hG.natCard_H2_zmod htriv)).exists_generator
  rw [Nat.card_congr (AddEquiv.addMonoidHomCongrRight
    (zmodAddEquivOfGenerator ha (hG.natCard_H2_zmod htriv))).symm.toEquiv,
    natCard_addMonoidHom_zmod hV]

/-- **Tate's duality map `α₂` of an infinite Demushkin group is bijective** on every finite
discrete `G`-module `M` killed by `p`: `H²(G, M) × H⁰(G, M') → H²(G, 𝔽_p)` is a perfect pairing.
It is injective by the dévissage, and `H²(G, M)` and `H⁰(G, M')` have the same finite order, since
`α₀` is bijective on `M'` and `M` is its own double dual. -/
theorem dualityMap2_bijective : Function.Bijective (dualityMap2 G M (ZMod p)) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hM' : ∀ φ : InternalHom G M (ZMod p), p • φ = 0 :=
    InternalHom.nsmul_eq_zero (ZModModule.char_nsmul_eq_zero p)
  have := hG.finite_H2 M (isPPrimaryTorsion_iff.2 fun m ↦ ⟨1, by rw [pow_one, hM]⟩)
  have : Finite (H2 G (ZMod p)) :=
    Nat.finite_of_card_ne_zero ((hG.natCard_H2_zmod htriv).trans_ne (Fact.out : p.Prime).ne_zero)
  have : Finite (H0 G (InternalHom G M (ZMod p)) →+ H2 G (ZMod p)) :=
    Finite.of_injective _ DFunLike.coe_injective
  refine (hG.dualityMap2_injective htriv M hM).bijective_of_nat_card_le (le_of_eq ?_)
  -- `|Hom(H⁰(M'), H²(𝔽_p))| = |H⁰(M')| = |Hom(H²(M''), H²(𝔽_p))| = |H²(M'')| = |H²(M)|`. The
  -- double dual `M''` is only ever named through the terms that produce it: writing its type out
  -- picks instance paths on `ZMod p` that Lean cannot identify with the ones in the duality maps.
  have h₁ : Nat.card (H0 G (InternalHom G M (ZMod p)) →+ H2 G (ZMod p)) =
      Nat.card (H0 G (InternalHom G M (ZMod p))) :=
    hG.natCard_addMonoidHom_H2 htriv _ fun v ↦ Subtype.ext (by simpa using hM' v)
  have hbij : Function.Bijective (dualityMap0 G (InternalHom G M (ZMod p)) (ZMod p)) :=
    hG.dualityMap0_bijective htriv (InternalHom G M (ZMod p)) hM'
  have hfin : Finite (H2 G (InternalHom G (InternalHom G M (ZMod p)) (ZMod p))) :=
    hG.finite_H2 _ (isPPrimaryTorsion_iff.2 fun m ↦ ⟨1, by
      rw [pow_one]; exact InternalHom.nsmul_eq_zero (ZModModule.char_nsmul_eq_zero p) m⟩)
  have h₂₃ := (Nat.card_congr (Equiv.ofBijective _ hbij)).trans
    (hG.natCard_addMonoidHom_H2 htriv _
      (nsmul_H2_eq_zero (InternalHom.nsmul_eq_zero (ZModModule.char_nsmul_eq_zero p))))
  have hev : Function.Bijective (InternalHom.eval G M (ZMod p)).toAddMonoidHom :=
    InternalHom.eval_bijective hM
  have h₂₃₄ := h₂₃.trans (Nat.card_congr (explicitCoeff2Equiv G M (AddEquiv.ofBijective _ hev)
    continuous_of_discreteTopology continuous_of_discreteTopology
    fun g m ↦ map_smul (InternalHom.eval G M (ZMod p)) g m).symm.toEquiv)
  exact h₁.trans h₂₃₄

end IsDemushkin

end TauCeti
