/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Duality.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.TwistedCoefficients

/-!
# Tate's duality maps of a Demushkin group with twisted coefficients

Let `G` be an infinite Demushkin group with canonical character `χ = demushkinCharacter hG`, and let
`I(χ)/pⁱ = TauCeti.ZModTwist χ i` be the twisted coefficients `ℤ/pⁱ` on which `G` acts through `χ`,
so that `H²(G, I(χ)/pⁱ)` is cyclic of order `pⁱ`
(`TauCeti.IsDemushkin.isAddCyclic_H2_zModTwist_demushkinCharacter`). For a finite discrete
`G`-module `M`, Tate's duality maps with these coefficients are

`αⱼ : Hʲ(G, M) → Hom(H²⁻ʲ(G, Hom(M, I(χ)/pⁱ)), H²(G, I(χ)/pⁱ))`, `j = 0, 1, 2`,

the cup products with the evaluation pairing (`TauCeti.ContCohomology.dualityMap0`, `dualityMap1`,
`dualityMap2`). This file proves **Tate's duality at level `pⁱ`**: the three maps are bijective on
every finite discrete `G`-module `M` killed by `pⁱ`, so that the pairings

`Hʲ(G, M) × H²⁻ʲ(G, Hom(M, I(χ)/pⁱ)) → H²(G, I(χ)/pⁱ) ≅ ℤ/pⁱ`

are perfect pairings of finite abelian groups. The argument has three steps.

* **Modules killed by `p`.** Multiplication by `pⁱ⁻¹` is an injective `G`-map
  `I(χ)/p →+[G] I(χ)/pⁱ` whose range is the `p`-torsion of `I(χ)/pⁱ`, and the induced map
  `H²(G, I(χ)/p) → H²(G, I(χ)/pⁱ)` is injective, by the prescription property of `χ`, with range
  the `p`-torsion of the cyclic group `H²(G, I(χ)/pⁱ)`, by counting
  (`TauCeti.IsDemushkin.exists_explicitCoeff2_mulPow_eq_of_nsmul_eq_zero`). On a module `M`
  killed by `p`, the internal homs `Hom(M, I(χ)/p)` and `Hom(M, I(χ)/pⁱ)` are therefore
  identified, and every homomorphism from the `p`-torsion group `H²⁻ʲ(G, Hom(M, I(χ)/p))` to
  `H²(G, I(χ)/pⁱ)` factors through `H²(G, I(χ)/p)`; so each `αⱼ` at level `pⁱ` is the one at level
  `p` read through these identifications
  (`TauCeti.ContCohomology.dualityMap0_bijective_of_injective_of_forall_nsmul_eq_zero` and its
  companions), and `I(χ)/p` is `𝔽_p` with trivial action, where the duality is
  `TauCeti.IsDemushkin.dualityMap0_bijective`, `dualityMap1_bijective`, `dualityMap2_bijective`.
* **Dévissage.** Tate's dévissage over the order of `M` for an infinite pro-`p` group
  (`TauCeti.IsProP.dualityMap0_bijective_dualityMap1_bijective_dualityMap2_injective`), whose base
  case is the first step on the trivial modules of order `p`, applies because both `I(χ)/pⁱ` and
  `H²(G, I(χ)/pⁱ) ≅ ℤ/pⁱ` satisfy Baer's criterion over `ℤ/pⁱ`. It gives `α₀` and `α₁` bijective
  and `α₂` injective.
* **Counting.** `α₂` is then bijective by the general count
  `TauCeti.ContCohomology.dualityMap2_bijective_of_injective_of_addEquiv_zmod`, as both `I(χ)/pⁱ`
  and `H²(G, I(χ)/pⁱ)` are `ℤ/pⁱ`: `|H²(G, M)| = |H⁰(G, Hom(M, I(χ)/pⁱ))|`, since `α₀` is bijective
  on the dual module and `M` is its own double dual with values in `I(χ)/pⁱ`.

## Main results

* `TauCeti.IsDemushkin.dualityMap0_zModTwist_bijective`,
  `TauCeti.IsDemushkin.dualityMap1_zModTwist_bijective`,
  `TauCeti.IsDemushkin.dualityMap2_zModTwist_bijective`: **Tate's duality at level `pⁱ`**: for an
  infinite Demushkin group and a finite discrete `G`-module `M` killed by `pⁱ`, Tate's duality maps
  with coefficients `I(χ)/pⁱ` are bijective.

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

/-! ### Modules killed by `p`: reduction to the duality at `𝔽_p` -/

section KilledByP

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

/-- **Tate's duality maps with coefficients `I(χ)/pⁱ` on a module killed by `p`**, `i ≥ 1`: the
three maps are bijective, since they are the duality maps at level `p` read through the
identification of `Hom(M, I(χ)/p)` with `Hom(M, I(χ)/pⁱ)` and of `H²(G, I(χ)/p)` with the
`p`-torsion of `H²(G, I(χ)/pⁱ)`. This is the base case of the dévissage over the order of `M`. -/
private theorem dualityMap_zModTwist_bijective_of_nsmul_eq_zero :
    Function.Bijective (dualityMap0 G M (ZModTwist (demushkinCharacter hG) i)) ∧
      Function.Bijective (dualityMap1 G M (ZModTwist (demushkinCharacter hG) i)) ∧
        Function.Bijective (dualityMap2 G M (ZModTwist (demushkinCharacter hG) i)) :=
  have hinj := (hasPrescriptionProperty_demushkinCharacter hG).injective_explicitCoeff2_mulPow
    (Nat.add_sub_cancel' hi)
  have h₁ := hG.dualityMap_zModTwist_one_bijective M hM
  ⟨dualityMap0_bijective_of_injective_of_forall_nsmul_eq_zero _ hM
      (ZModTwist.mulPow_injective _ _) (hG.exists_mulPow_eq hi) hinj
      (hG.exists_explicitCoeff2_mulPow_eq hi) h₁.1,
    dualityMap1_bijective_of_injective_of_forall_nsmul_eq_zero _ hM
      (ZModTwist.mulPow_injective _ _) (hG.exists_mulPow_eq hi) hinj
      (hG.exists_explicitCoeff2_mulPow_eq hi) h₁.2.1,
    dualityMap2_bijective_of_injective_of_forall_nsmul_eq_zero _ hM
      (ZModTwist.mulPow_injective _ _) (hG.exists_mulPow_eq hi) hinj
      (hG.exists_explicitCoeff2_mulPow_eq hi) h₁.2.2⟩

end KilledByP

/-! ### Dévissage over the order of `M` and the duality at level `pⁱ` -/

section Devissage

variable (i : ℕ)

/-- On a module of order `p` killed by `pⁱ`, the three duality maps with coefficients `I(χ)/pⁱ` are
bijective, in the weaker form the dévissage consumes. For `i = 0` no such module exists. -/
private theorem dualityMap_zModTwist_of_natCard_eq (A : Type u) [AddCommGroup A]
    [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A] [ContinuousSMul G A]
    [Finite A] (hA : Nat.card A = p) (hAi : ∀ a : A, p ^ i • a = 0) :
    Function.Surjective (dualityMap0 G A (ZModTwist (demushkinCharacter hG) i)) ∧
      Function.Bijective (dualityMap1 G A (ZModTwist (demushkinCharacter hG) i)) ∧
        Function.Injective (dualityMap2 G A (ZModTwist (demushkinCharacter hG) i)) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · -- a module killed by `p ^ 0 = 1` is trivial, so it cannot have order `p`
    have : Subsingleton A := subsingleton_of_forall_eq 0 fun a ↦ by simpa using hAi a
    exact absurd (hA.symm.trans (Nat.card_of_subsingleton (0 : A)))
      (Fact.out : p.Prime).one_lt.ne'
  · have hd := hG.dualityMap_zModTwist_bijective_of_nsmul_eq_zero hi A
      fun a ↦ hA ▸ card_nsmul_eq_zero'
    exact ⟨hd.1.2, hd.2.1, hd.2.2.1⟩

variable (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M] [Finite M] (hM : ∀ x : M, p ^ i • x = 0)

include hM

/-- **The dévissage of Tate's duality maps at level `pⁱ`.** On every finite discrete `G`-module `M`
killed by `pⁱ`, `α₀` and `α₁` are bijective and `α₂` is injective: the dévissage
`TauCeti.IsProP.dualityMap0_bijective_dualityMap1_bijective_dualityMap2_injective` of an infinite
pro-`p` group, with `n = pⁱ` and `N = I(χ)/pⁱ`, whose Baer hypotheses hold because `I(χ)/pⁱ` and
`H²(G, I(χ)/pⁱ)` are both `ℤ/pⁱ`. -/
private theorem dualityMap_zModTwist_devissage :
    Function.Bijective (dualityMap0 G M (ZModTwist (demushkinCharacter hG) i)) ∧
      Function.Bijective (dualityMap1 G M (ZModTwist (demushkinCharacter hG) i)) ∧
        Function.Injective (dualityMap2 G M (ZModTwist (demushkinCharacter hG) i)) :=
  hG.isProP.dualityMap0_bijective_dualityMap1_bijective_dualityMap2_injective _
    (ZModTwist.moduleBaer _ i) (hG.moduleBaer_H2_zModTwist_demushkinCharacter i)
    (fun A _ _ _ _ _ _ hA _ hAi ↦ hG.dualityMap_zModTwist_of_natCard_eq i A hA hAi) M
    (isPPrimaryTorsion_iff.2 fun m ↦ ⟨i, hM m⟩) hM

/-- **Tate's duality map `α₀` of an infinite Demushkin group with coefficients `I(χ)/pⁱ` is
bijective** on every finite discrete `G`-module `M` killed by `pⁱ`:
`H⁰(G, M) × H²(G, Hom(M, I(χ)/pⁱ)) → H²(G, I(χ)/pⁱ)` is a perfect pairing. Injectivity is the
general `TauCeti.IsProP.dualityMap0_injective`, from the co-effaceability of `H⁰`. -/
theorem dualityMap0_zModTwist_bijective :
    Function.Bijective (dualityMap0 G M (ZModTwist (demushkinCharacter hG) i)) :=
  (hG.dualityMap_zModTwist_devissage i M hM).1

/-- **Tate's duality map `α₁` of an infinite Demushkin group with coefficients `I(χ)/pⁱ` is
bijective** on every finite discrete `G`-module `M` killed by `pⁱ`:
`H¹(G, M) × H¹(G, Hom(M, I(χ)/pⁱ)) → H²(G, I(χ)/pⁱ)` is a perfect pairing. -/
theorem dualityMap1_zModTwist_bijective :
    Function.Bijective (dualityMap1 G M (ZModTwist (demushkinCharacter hG) i)) :=
  (hG.dualityMap_zModTwist_devissage i M hM).2.1

/-- **Tate's duality map `α₂` of an infinite Demushkin group with coefficients `I(χ)/pⁱ` is
bijective** on every finite discrete `G`-module `M` killed by `pⁱ`:
`H²(G, M) × H⁰(G, Hom(M, I(χ)/pⁱ)) → H²(G, I(χ)/pⁱ)` is a perfect pairing. It is injective by the
dévissage and bijective by counting
(`TauCeti.ContCohomology.dualityMap2_bijective_of_injective_of_addEquiv_zmod`), since `α₀` is
bijective on `Hom(M, I(χ)/pⁱ)` and both `I(χ)/pⁱ` and `H²(G, I(χ)/pⁱ)` are `ℤ/pⁱ`. -/
theorem dualityMap2_zModTwist_bijective :
    Function.Bijective (dualityMap2 G M (ZModTwist (demushkinCharacter hG) i)) := by
  have : NeZero (p ^ i) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hM' : ∀ φ : InternalHom G M (ZModTwist (demushkinCharacter hG) i), p ^ i • φ = 0 :=
    InternalHom.nsmul_eq_zero_of_domain hM
  have := hG.finite_H2 (InternalHom G (InternalHom G M (ZModTwist (demushkinCharacter hG) i))
    (ZModTwist (demushkinCharacter hG) i))
    (isPPrimaryTorsion_iff.2 fun m ↦ ⟨i, InternalHom.nsmul_eq_zero_of_domain hM' m⟩)
  obtain ⟨e₂⟩ := hG.nonempty_addEquiv_H2_zModTwist_demushkinCharacter_zmod i
  exact dualityMap2_bijective_of_injective_of_addEquiv_zmod (ZModTwist.equiv _ i) e₂ hM
    (hG.dualityMap0_zModTwist_bijective i _ hM') (hG.dualityMap_zModTwist_devissage i M hM).2.2

end Devissage

end IsDemushkin

end TauCeti
