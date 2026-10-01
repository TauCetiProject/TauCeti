/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Duality.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.TwistedCoefficients

/-!
# Tate's duality maps of a Demushkin group with twisted coefficients, on modules killed by `p`

Let `G` be an infinite Demushkin group with canonical character `χ = demushkinCharacter hG`, and let
`I(χ)/pⁱ = TauCeti.ZModTwist χ i` be the twisted coefficients `ℤ/pⁱ` on which `G` acts through `χ`,
so that `H²(G, I(χ)/pⁱ)` is cyclic of order `pⁱ`
(`TauCeti.IsDemushkin.isAddCyclic_H2_zModTwist_demushkinCharacter`). For a finite discrete
`G`-module `M`, Tate's duality maps with these coefficients are

`αⱼ : Hʲ(G, M) → Hom(H²⁻ʲ(G, Hom(M, I(χ)/pⁱ)), H²(G, I(χ)/pⁱ))`, `j = 0, 1, 2`,

the cup products with the evaluation pairing (`TauCeti.ContCohomology.dualityMap0`, `dualityMap1`,
`dualityMap2`), and the duality of `G` at level `pⁱ` says that they are bijective. This file proves
it for every `M` killed by `p`, which is the base case of the dévissage over the order of `M`.

The argument reduces to the duality at `𝔽_p` coefficients
(`TauCeti.IsDemushkin.dualityMap0_bijective`, `dualityMap1_bijective`, `dualityMap2_bijective`).
Multiplication by `pⁱ⁻¹` is an injective `G`-map `I(χ)/p →+[G] I(χ)/pⁱ` whose range is the
`p`-torsion of `I(χ)/pⁱ`, and the induced map `H²(G, I(χ)/p) → H²(G, I(χ)/pⁱ)` is injective, by the
prescription property of `χ`, with range the `p`-torsion of the cyclic group `H²(G, I(χ)/pⁱ)`, by
counting (`TauCeti.IsDemushkin.exists_explicitCoeff2_mulPow_eq_of_nsmul_eq_zero`). On a module `M`
killed by `p`, the internal homs `Hom(M, I(χ)/p)` and `Hom(M, I(χ)/pⁱ)` are therefore identified,
and every homomorphism from the `p`-torsion group `H²⁻ʲ(G, Hom(M, I(χ)/p))` to `H²(G, I(χ)/pⁱ)`
factors through `H²(G, I(χ)/p)`; so each `αⱼ` at level `pⁱ` is the one at level `p` read through
these identifications (`TauCeti.ContCohomology.explicitCoeff2_dualityMap0` and its companions).
Finally `I(χ)/p` is `𝔽_p` with trivial action, because a pro-`p` group acts trivially on it.

## Main results

* `TauCeti.IsDemushkin.dualityMap0_zModTwist_bijective`,
  `TauCeti.IsDemushkin.dualityMap1_zModTwist_bijective`,
  `TauCeti.IsDemushkin.dualityMap2_zModTwist_bijective`: for an infinite Demushkin group, `i ≥ 1`
  and a finite discrete `G`-module `M` killed by `p`, Tate's duality maps with coefficients
  `I(χ)/pⁱ` are bijective: the pairings `Hʲ(G, M) × H²⁻ʲ(G, Hom(M, I(χ)/pⁱ)) → H²(G, I(χ)/pⁱ)` are
  perfect.

## References

* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki 8
  (1962/63), exposé 252, §9.
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §2.
-/

public section

namespace TauCeti

open TauCeti.ContCohomology

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the duality at
-- `𝔽_p` coefficients, stated under the same preference, applies to `ZMod p` here.
attribute [local instance 2000] Ring.toAddCommGroup

universe u

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] [Infinite G] (hG : IsDemushkin p G)

namespace IsDemushkin

include hG

variable {i : ℕ} (hi : 0 < i)
include hi

omit [Infinite G] in
/-- The `p`-torsion of `I(χ)/pⁱ` is the image of `I(χ)/p` under multiplication by `pⁱ⁻¹`, in the
form the transport along `mulPow` consumes. -/
private theorem exists_mulPow_eq (y : ZModTwist (demushkinCharacter hG) i) (hy : p • y = 0) :
    ∃ x, ZModTwist.mulPow (demushkinCharacter hG) (Nat.add_sub_cancel' hi) x = y :=
  ZModTwist.exists_mulPow_eq_of_nsmul_eq_zero _ _ (by rwa [pow_one])

/-- The `p`-torsion of `H²(G, I(χ)/pⁱ)` is the image of `H²(G, I(χ)/p)` under multiplication by
`pⁱ⁻¹`, in the form the transport along `mulPow` consumes. -/
private theorem exists_explicitCoeff2_mulPow_eq (y : H2 G (ZModTwist (demushkinCharacter hG) i))
    (hy : p • y = 0) :
    ∃ x, explicitCoeff2 G (ZModTwist (demushkinCharacter hG) 1)
      (ZModTwist.mulPow (demushkinCharacter hG) (Nat.add_sub_cancel' hi))
      continuous_of_discreteTopology x = y :=
  hG.exists_explicitCoeff2_mulPow_eq_of_nsmul_eq_zero _ (by rwa [pow_one])

omit hi

variable (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M] [Finite M] (hM : ∀ x : M, p • x = 0)

include hM

/-- The three duality maps at the bottom level `I(χ)/p`, which is `𝔽_p` with trivial action. -/
private theorem dualityMap_zModTwist_one_bijective :
    Function.Bijective (dualityMap0 G M (ZModTwist (demushkinCharacter hG) 1)) ∧
      Function.Bijective (dualityMap1 G M (ZModTwist (demushkinCharacter hG) 1)) ∧
        Function.Bijective (dualityMap2 G M (ZModTwist (demushkinCharacter hG) 1)) := by
  -- The duality at `𝔽_p` coefficients is stated for a trivial action of `G` on `ZMod p`.
  let : DistribMulAction G (ZMod p) := DistribMulAction.compHom (ZMod p) (1 : G →* (ZMod p)ˣ)
  have htriv : ∀ (g : G) (m : ZMod p), g • m = m := fun _ m ↦ one_smul (ZMod p)ˣ m
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd.congr fun x ↦ (htriv x.1 x.2).symm⟩
  let e₀ : ZMod p ≃+ ZModTwist (demushkinCharacter hG) 1 :=
    (ZMod.ringEquivCongr (pow_one p).symm).toAddEquiv.trans (ZModTwist.equiv _ 1).symm
  let e : ZMod p →+[G] ZModTwist (demushkinCharacter hG) 1 :=
    { e₀.toAddMonoidHom with
      map_smul' := fun g a ↦ by
        rw [MonoidHom.id_apply, htriv, hG.isProP.smul_zModTwist_one_eq_self] }
  have he : Function.Bijective e := e₀.bijective
  have hH := explicitCoeff2_bijective G (ZMod p) (f := e) he
  exact ⟨dualityMap0_bijective_of_injective_of_forall_nsmul_eq_zero e hM he.1 (fun y _ ↦ he.2 y)
      hH.1 (fun y _ ↦ hH.2 y) (hG.dualityMap0_bijective htriv M hM),
    dualityMap1_bijective_of_injective_of_forall_nsmul_eq_zero e hM he.1 (fun y _ ↦ he.2 y)
      hH.1 (fun y _ ↦ hH.2 y) (hG.dualityMap1_bijective htriv M hM),
    dualityMap2_bijective_of_injective_of_forall_nsmul_eq_zero e hM he.1 (fun y _ ↦ he.2 y)
      hH.1 (fun y _ ↦ hH.2 y) (hG.dualityMap2_bijective htriv M hM)⟩

include hi

/-- **Tate's duality map `α₀` of an infinite Demushkin group with coefficients `I(χ)/pⁱ` is
bijective** on every finite discrete `G`-module `M` killed by `p`, for `i ≥ 1`:
`H⁰(G, M) × H²(G, Hom(M, I(χ)/pⁱ)) → H²(G, I(χ)/pⁱ)` is a perfect pairing. -/
theorem dualityMap0_zModTwist_bijective :
    Function.Bijective (dualityMap0 G M (ZModTwist (demushkinCharacter hG) i)) :=
  dualityMap0_bijective_of_injective_of_forall_nsmul_eq_zero _ hM
    (ZModTwist.mulPow_injective _ _) (hG.exists_mulPow_eq hi)
    ((hasPrescriptionProperty_demushkinCharacter hG).injective_explicitCoeff2_mulPow _)
    (hG.exists_explicitCoeff2_mulPow_eq hi) (hG.dualityMap_zModTwist_one_bijective M hM).1

/-- **Tate's duality map `α₁` of an infinite Demushkin group with coefficients `I(χ)/pⁱ` is
bijective** on every finite discrete `G`-module `M` killed by `p`, for `i ≥ 1`:
`H¹(G, M) × H¹(G, Hom(M, I(χ)/pⁱ)) → H²(G, I(χ)/pⁱ)` is a perfect pairing. -/
theorem dualityMap1_zModTwist_bijective :
    Function.Bijective (dualityMap1 G M (ZModTwist (demushkinCharacter hG) i)) :=
  dualityMap1_bijective_of_injective_of_forall_nsmul_eq_zero _ hM
    (ZModTwist.mulPow_injective _ _) (hG.exists_mulPow_eq hi)
    ((hasPrescriptionProperty_demushkinCharacter hG).injective_explicitCoeff2_mulPow _)
    (hG.exists_explicitCoeff2_mulPow_eq hi) (hG.dualityMap_zModTwist_one_bijective M hM).2.1

/-- **Tate's duality map `α₂` of an infinite Demushkin group with coefficients `I(χ)/pⁱ` is
bijective** on every finite discrete `G`-module `M` killed by `p`, for `i ≥ 1`:
`H²(G, M) × H⁰(G, Hom(M, I(χ)/pⁱ)) → H²(G, I(χ)/pⁱ)` is a perfect pairing. -/
theorem dualityMap2_zModTwist_bijective :
    Function.Bijective (dualityMap2 G M (ZModTwist (demushkinCharacter hG) i)) :=
  dualityMap2_bijective_of_injective_of_forall_nsmul_eq_zero _ hM
    (ZModTwist.mulPow_injective _ _) (hG.exists_mulPow_eq hi)
    ((hasPrescriptionProperty_demushkinCharacter hG).injective_explicitCoeff2_mulPow _)
    (hG.exists_explicitCoeff2_mulPow_eq hi) (hG.dualityMap_zModTwist_one_bijective M hM).2.2

end IsDemushkin

end TauCeti
