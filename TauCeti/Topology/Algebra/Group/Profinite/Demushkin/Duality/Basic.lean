/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZMod.Injective
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Cup
public import TauCeti.RingTheory.SimpleModule.InjectiveProjective
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.CupForm
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.TateDuality
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

The dévissage is the general one for pro-`p` groups
(`TauCeti.IsProP.dualityMap0_surjective_dualityMap1_injective` and
`TauCeti.IsProP.dualityMap1_surjective_dualityMap2_injective`, with `N = 𝔽_p` and `n = p`): every
finite `𝔽_p[G]`-module of a pro-`p` group is an iterated extension
of trivial modules of order `p`, and the four lemmas along a short exact sequence carry
surjectivity of `α₀`, bijectivity of `α₁` and injectivity of `α₂` from the two ends of an
extension to its middle; the Baer hypothesis on `H²(G, 𝔽_p)` holds because it is an
`𝔽_p`-vector space. Two further arguments, both needing `G` infinite, complete the duality.
Injectivity of `α₀` on `M` is the general `TauCeti.IsProP.dualityMap0_injective`: it follows from
injectivity of `α₁` on the kernel of a trace `Coind_V^G M → M` that vanishes on invariants, which
exists because `H⁰` is co-effaceable on an infinite pro-`p` group. Surjectivity of `α₂` on `M` is
then the general count `TauCeti.ContCohomology.dualityMap2_bijective_of_injective_of_addEquiv_zmod`:
`H²(G, 𝔽_p)` is `𝔽_p`, and injectivity of `α₂` on `M` and of `α₀` on `M'` together with the double
duality `M ≅ M''` give `|H²(G, M)| = |H⁰(G, M')|`.

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

/-- On a trivial `G`-module of order `p`, which is `𝔽_p` up to a `G`-equivariant isomorphism, the
three duality maps of a Demushkin group are bijective, here in the form consumed by the dévissages
`TauCeti.IsProP.dualityMap0_surjective_dualityMap1_injective` and
`TauCeti.IsProP.dualityMap1_surjective_dualityMap2_injective`. -/
private theorem dualityMap_of_natCard_eq (A : Type u) [AddCommGroup A] [TopologicalSpace A]
    [DiscreteTopology A] [DistribMulAction G A] [ContinuousSMul G A] [Finite A]
    (hA : Nat.card A = p) (htrivA : ∀ (g : G) (a : A), g • a = a) :
    Function.Surjective (dualityMap0 G A (ZMod p)) ∧
      Function.Bijective (dualityMap1 G A (ZMod p)) ∧
        Function.Injective (dualityMap2 G A (ZMod p)) := by
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

/-- **The dévissage of Tate's duality argument.** On every finite discrete `G`-module `M` killed
by `p`, `α₀` is surjective, `α₁` is bijective and `α₂` is injective: this holds on the trivial
modules of order `p`, which are `𝔽_p`, and passes through extensions by the four lemmas, the
dévissage `TauCeti.IsProP.dualityMap0_surjective_dualityMap1_bijective_dualityMap2_injective` with
`n = p` and `N = 𝔽_p`, whose Baer hypothesis on `H²(G, 𝔽_p)` holds because it is an
`𝔽_p`-vector space. -/
private theorem dualityMap_devissage (M : Type u) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
    (hM : ∀ x : M, p • x = 0) :
    Function.Surjective (dualityMap0 G M (ZMod p)) ∧
      Function.Bijective (dualityMap1 G M (ZMod p)) ∧
        Function.Injective (dualityMap2 G M (ZMod p)) :=
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  hG.isProP.dualityMap0_surjective_dualityMap1_bijective_dualityMap2_injective (ZMod p)
    (Module.Baer.zmod_self p) (Module.Baer.of_isSemisimpleRing (ZMod p) (H2 G (ZMod p)))
    (fun A _ _ _ _ _ _ hA htrivA _ ↦ hG.dualityMap_of_natCard_eq htriv A hA htrivA) M
    (isPPrimaryTorsion_iff.2 fun m ↦ ⟨1, by rw [pow_one, hM]⟩) hM

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
discrete `G`-module `M` killed by `p`: the general `TauCeti.IsProP.dualityMap0_injective`, whose
trace along a deep enough open subgroup vanishes on invariants, with `α₁` injective on its kernel
by the dévissage. -/
theorem dualityMap0_injective : Function.Injective (dualityMap0 G M (ZMod p)) :=
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  hG.isProP.dualityMap0_injective (ZMod p) (Module.Baer.zmod_self p)
    (Module.Baer.of_isSemisimpleRing (ZMod p) _)
    (fun A _ _ _ _ _ _ hA htrivA _ ↦
      have hd := hG.dualityMap_of_natCard_eq htriv A hA htrivA
      ⟨hd.1, hd.2.1.1⟩) M
    (isPPrimaryTorsion_iff.2 fun m ↦ ⟨1, by rw [pow_one, hM]⟩) hM

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
/-- The explicit `H²(G, 𝔽_p)` of a Demushkin group is `𝔽_p`, being of order `p`. -/
private theorem nonempty_addEquiv_H2_zmod : Nonempty (H2 G (ZMod p) ≃+ ZMod p) :=
  ⟨addEquivOfPrimeCardEq (hG.natCard_H2_zmod htriv) (Nat.card_zmod p)⟩

omit [TotallyDisconnectedSpace G] [Infinite G] hM in
/-- **Homomorphisms into `H²(G, 𝔽_p)` of a Demushkin group are as many as their source**: for a
finite abelian group `V` killed by `p`, `|Hom(V, H²(G, 𝔽_p))| = |V|`, since `H²(G, 𝔽_p)` is
one-dimensional over `𝔽_p`. -/
theorem natCard_addMonoidHom_H2 (V : Type*) [AddCommGroup V] [Finite V]
    (hV : ∀ v : V, p • v = 0) : Nat.card (V →+ H2 G (ZMod p)) = Nat.card V :=
  (hG.nonempty_addEquiv_H2_zmod htriv).elim fun e ↦ natCard_addMonoidHom_of_addEquiv_zmod e hV

/-- **Tate's duality map `α₂` of an infinite Demushkin group is bijective** on every finite
discrete `G`-module `M` killed by `p`: `H²(G, M) × H⁰(G, M') → H²(G, 𝔽_p)` is a perfect pairing,
where `M' = Hom(M, 𝔽_p)`. It is injective by the dévissage and bijective by counting
(`TauCeti.ContCohomology.dualityMap2_bijective_of_injective_of_addEquiv_zmod`), since `α₀` is
injective on `M'` and `H²(G, 𝔽_p)` is `𝔽_p`. -/
theorem dualityMap2_bijective : Function.Bijective (dualityMap2 G M (ZMod p)) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hM' : ∀ φ : InternalHom G M (ZMod p), p • φ = 0 := InternalHom.nsmul_eq_zero_of_domain hM
  obtain ⟨e₂⟩ := hG.nonempty_addEquiv_H2_zmod htriv
  exact dualityMap2_bijective_of_injective_of_addEquiv_zmod (AddEquiv.refl _) e₂ hM
    (hG.dualityMap0_injective htriv _ hM') (hG.dualityMap2_injective htriv M hM)

end IsDemushkin

end TauCeti
