/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Map
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Conjugation.AllDegrees
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Norm.Naturality
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

/-!
# Restriction of the Evens norm along a single double coset, and conjugation

Let `U` be a compact open subgroup of finite index in a topological group `G`, with Evens norm
`N_U^G : Hⁿ(U, 𝔽₂) → H^{[G : U] n}(G, 𝔽₂)`. The double-coset formula of Evens (1963), §6, expresses
the pullback of `N_U^G x` along a continuous homomorphism `φ : H → G` as a cup product over the
double cosets `φ(H) \ G / U`, with one Evens norm for each. This file proves the formula when there
is only one double coset `φ(H) s U = G`: then

```
φ^* (N_U^G x) = N_{H_s}^H (ψ_s^* x)      in H^{[G : U] n}(H, 𝔽₂),
```

where `ψ_s : H → G` is the conjugate `h ↦ s⁻¹ φ(h) s` of `φ`, and `H_s = ψ_s⁻¹(U)`, restricted
along which `ψ_s` maps into `U` (`OpenSubgroup.trivialF2Map_evensNorm_of_surjective`). The
condition `φ(H) s U = G` says that `H` acts transitively on `G ⧸ U` through `ψ_s`; then `ψ_s`
induces a bijection `H ⧸ H_s ≃ G ⧸ U`
(`TauCeti.QuotientGroup.congrComapOfSurjectiveMk`), so `[H : H_s] = [G : U]` and the
naturality of the norm in the group (`OpenSubgroup.trivialF2Map_evensNorm`) applies to `ψ_s`.
Pulling back along `φ` and along `ψ_s` agree on `H^*(G, 𝔽₂)`, because inner automorphisms act
trivially on cohomology (`TauCeti.trivialF2Map_eq_of_conj`).

For the inclusion `φ` of a subgroup `K` with `KsU = G`, where pulling back along `φ` is
restriction (`TauCeti.trivialF2Map_subgroupSubtype`), this is the restriction formula
`res_K (N_U^G x) = N_{K ∩ sUs⁻¹}^K (ψ_s^* x)`, with `ψ_s : K ∩ sUs⁻¹ → U`, `k ↦ s⁻¹ k s`. For the
identity of `G` and `s = g`, it is the invariance of the norm under conjugation: for
`V = gUg⁻¹`, the norm from `V` of the conjugate of `x` is the norm of `x`
(`OpenSubgroup.evensNorm_trivialF2Map_conjHom`), the multiplicative counterpart of
`TauCeti.ContinuousCohomology.conjMap_comp_corestriction` for corestriction.

## Main results

* `OpenSubgroup.trivialF2Map_evensNorm_of_surjective`: the double-coset formula for the Evens norm
  along a continuous homomorphism, when there is a single double coset.
* `OpenSubgroup.evensNorm_trivialF2Map_conjHom`: the Evens norm is invariant under conjugation.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), Sections 2–6.
-/

public section

namespace OpenSubgroup

open TauCeti

universe u

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (U : OpenSubgroup G) [U.toSubgroup.FiniteIndex] [CompactSpace U.toSubgroup]
  [Fintype (G ⧸ U.toSubgroup)]

/-- **The double-coset formula for the Evens norm with a single double coset.** Let
`φ : H → G` be a continuous homomorphism, `s : G`, and `ψ h = s⁻¹ φ(h) s` the conjugate of `φ`.
If `H` acts transitively on `G ⧸ U` through `ψ`, that is, `φ(H) s U = G`, then pulling back the
norm `N_U^G x` along `φ` gives the norm from `ψ⁻¹(U)` of the pullback of `x` along `ψ`:
`φ^* (N_U^G x) = N_{ψ⁻¹(U)}^H (ψ^* x)`, after transporting the degree `[H : ψ⁻¹(U)] n` to
`[G : U] n`. -/
theorem trivialF2Map_evensNorm_of_surjective (φ ψ : H →ₜ* G) (s : G)
    (hψ : ∀ h, ψ h = s⁻¹ * φ h * s)
    (hsurj : Function.Surjective fun h : H ↦ (ψ h : G ⧸ U.toSubgroup))
    [CompactSpace (U.comap (ψ : H →* G) ψ.continuous).toSubgroup]
    [Fintype (H ⧸ (U.comap (ψ : H →* G) ψ.continuous).toSubgroup)] {n : ℕ}
    (x : continuousCohomology n (trivialF2 U.toSubgroup)) :
    trivialF2Map φ (Fintype.card (G ⧸ U.toSubgroup) * n) (U.evensNorm x) =
      (ContinuousCohomology.degreeCast (trivialF2 H) (by
        rw [Fintype.card_congr (α := H ⧸ (U.comap (ψ : H →* G) ψ.continuous).toSubgroup)
          (QuotientGroup.congrComapOfSurjectiveMk (ψ : H →* G) U.toSubgroup hsurj)])).hom
        ((U.comap (ψ : H →* G) ψ.continuous).evensNorm
          (trivialF2Map (ψ.subgroupComap U.toSubgroup) n x)) := by
  have : LocallyCompactSpace G :=
    (isCompact_iff_compactSpace.2
      ‹CompactSpace U.toSubgroup›).locallyCompactSpace_of_mem_nhds_of_group
        (U.isOpen'.mem_nhds U.one_mem)
  -- Pulling back along `φ` and along its conjugate `ψ` agree on the cohomology of `G`.
  rw [← trivialF2Map_eq_of_conj φ ψ s⁻¹ (fun h ↦ by rw [hψ, inv_inv])]
  -- `ψ.subgroupComap U.toSubgroup` has domain `U.toSubgroup.comap ψ`, which is the underlying
  -- subgroup of `U.comap ψ _` by `OpenSubgroup.toSubgroup_comap`, an equality that holds by `rfl`.
  exact trivialF2Map_evensNorm (V := U.comap (ψ : H →* G) ψ.continuous) ψ
    (ψ.subgroupComap U.toSubgroup) (ψ.subgroupComap_apply_coe U.toSubgroup)
    (e := QuotientGroup.congrComapOfSurjectiveMk (ψ : H →* G) U.toSubgroup hsurj)
    (fun h ↦ QuotientGroup.congrComapOfSurjectiveMk_mk _ _ hsurj h) x

/-- **The Evens norm is invariant under conjugation.** For `g : G` and the conjugate
`V = gUg⁻¹` of `U`, the norm from `V` of the conjugate `(g)_* x` of `x ∈ Hⁿ(U, 𝔽₂)`, pulled back
along `ContinuousCohomology.conjHom`, `v ↦ g⁻¹ v g`, is the norm of `x`:
`N_V^G ((g)_* x) = N_U^G x`, after transporting the degree `[G : U] n` to `[G : V] n`. -/
theorem evensNorm_trivialF2Map_conjHom (V : OpenSubgroup G) [V.toSubgroup.FiniteIndex]
    [CompactSpace V.toSubgroup] [Fintype (G ⧸ V.toSubgroup)] (g : G)
    (hVU : V.toSubgroup = U.toSubgroup.map (MulAut.conj g).toMonoidHom) {n : ℕ}
    (x : continuousCohomology n (trivialF2 U.toSubgroup)) :
    V.evensNorm (trivialF2Map
        (ContinuousCohomology.conjHom U.toSubgroup V.toSubgroup g hVU) n x) =
      (ContinuousCohomology.degreeCast (trivialF2 G) (by
        rw [Fintype.card_congr (QuotientGroup.congrOfMapEq (MulAut.conj g) hVU.symm)])).hom
        (U.evensNorm x) := by
  -- `V` is the preimage of `U` under the conjugation `y ↦ g⁻¹ y g` of `G`, which restricts to
  -- `conjHom` on it and meets every coset of `U`.
  let c : G →ₜ* G := ContinuousMonoidHom.toContinuousMonoidHom (ContinuousAut.conj g⁻¹)
  have hc (y : G) : c y = g⁻¹ * y * g := by simp [c]
  obtain rfl : V = U.comap (c : G →* G) c.continuous := OpenSubgroup.toSubgroup_injective <| by
    ext y
    rw [hVU, Subgroup.mem_map_equiv]
    simp [hc]
  have hconj : ContinuousCohomology.conjHom U.toSubgroup _ g hVU = c.subgroupComap U.toSubgroup :=
    ContinuousMonoidHom.ext fun v ↦ Subtype.ext <|
      (ContinuousCohomology.coe_conjHom_apply _ _ g hVU v).trans
        ((hc v).symm.trans (c.subgroupComap_apply_coe U.toSubgroup v).symm)
  have key := trivialF2Map_evensNorm_of_surjective U (ContinuousMonoidHom.id G) c g
    (fun y ↦ hc y) (fun q ↦ by
      induction q using QuotientGroup.induction_on with | _ a =>
      exact ⟨g * a * g⁻¹, congrArg QuotientGroup.mk ((hc _).trans (by group))⟩) x
  rw [trivialF2Map_id, CategoryTheory.ConcreteCategory.id_apply] at key
  -- Transport `key` back to the degree `[G : V] n`.
  rw [hconj, key, ContinuousCohomology.degreeCast_hom_degreeCast_hom_apply,
    ContinuousCohomology.degreeCast_rfl, CategoryTheory.Iso.refl_hom,
    CategoryTheory.ConcreteCategory.id_apply]
  -- The two sides differ only in the implicit domain of `trivialF2Map`: the left side has
  -- `(U.comap c _).toSubgroup`, the codomain of `conjHom` that `hconj` rewrites at, and the right
  -- side has `U.toSubgroup.comap c`, the domain of `ContinuousMonoidHom.subgroupComap`. They agree
  -- by `OpenSubgroup.toSubgroup_comap`, which unfolds `OpenSubgroup.comap` and so holds by `rfl`
  -- at default transparency, but not at the reducible transparency at which `rw` closes goals.
  rfl

end OpenSubgroup
