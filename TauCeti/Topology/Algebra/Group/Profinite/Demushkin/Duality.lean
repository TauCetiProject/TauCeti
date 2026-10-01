/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Cup
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.CupForm

/-!
# Tate's duality maps of a Demushkin group at trivial coefficients

For a finite discrete `𝔽_p[G]`-module `M` of a pro-`p` group `G`, Tate's duality maps
`αᵢ : Hⁱ(G, M) → Hom(H²⁻ⁱ(G, M'), H²(G, 𝔽_p))`, with `M' = Hom(M, 𝔽_p)`, are the cup products
with the evaluation pairing (`TauCeti.ContCohomology.dualityMap0`, `dualityMap1`, `dualityMap2`).
For a Demushkin group they are isomorphisms for every such `M`: this is the perfect duality on its
finite modules, and the source of `cd_p G = 2`. Tate's proof (Serre's exposé, §9.1) is a dévissage
on `M` whose base case is the trivial module `M = 𝔽_p`, and this file proves that base case: for a
Demushkin group `G` and any trivial action of `G` on `ZMod p`, the three maps `α₀`, `α₁`, `α₂` at
`M = ZMod p` are bijective.

Under evaluation at `1` the dual module `Hom(𝔽_p, 𝔽_p)` is `𝔽_p` again, and the three maps read as
follows. `α₁` is the cup square `H¹(G, 𝔽_p) → Hom(H¹(G, 𝔽_p), H²(G, 𝔽_p))`, bijective because the
cup square of a Demushkin group is a perfect pairing (`TauCeti.IsDemushkin.cupFp_bijective`). `α₀`
sends `c ∈ 𝔽_p = H⁰(G, 𝔽_p)` to multiplication by `c` on `H²(G, 𝔽_p)`, bijective because
`H²(G, 𝔽_p)` is one-dimensional. `α₂` sends a class `b ∈ H²(G, 𝔽_p)` to `c ↦ c • b`, which is
bijective for every group acting trivially (`TauCeti.ContCohomology.dualityMap2_zmod_bijective`), so
no statement about it is specific to Demushkin groups.

## Main results

* `TauCeti.IsDemushkin.explicitCup11_mul_bijective`: on the explicit models, the cup product of
  multiplication on `H¹(G, 𝔽_p)` is a perfect pairing.
* `TauCeti.IsDemushkin.dualityMap1_bijective`, `TauCeti.IsDemushkin.dualityMap0_bijective`: Tate's
  duality maps `α₁` and `α₀` at `M = 𝔽_p` are bijective.

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
theorem dualityMap1_bijective : Function.Bijective (dualityMap1 G (ZMod p) (ZMod p)) := by
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
theorem dualityMap0_bijective : Function.Bijective (dualityMap0 G (ZMod p) (ZMod p)) :=
  dualityMap0_zmod_bijective_of_finrank_eq_one htriv
    ((cohomFpLinearEquivH2 p G htriv).finrank_eq.symm.trans hG.finrank_cohomFp_two)

end IsDemushkin

end TauCeti
