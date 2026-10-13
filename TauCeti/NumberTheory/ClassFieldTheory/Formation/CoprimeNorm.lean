/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.NormLimitation
import TauCeti.NumberTheory.Cyclotomic.FixingSubgroup

/-!
# Norm quotients under a base change of coprime degree

Let `V ◁ U` be a finite normal layer of a formation `A`, the layer `L/K` in field notation, and
let `V' ◁ U'` be a layer with `U' ≤ U` and `V' ≤ V`, the layer `L'/K'` for fields `K ⊆ K'` and
`L ⊆ L'`. If the degree `[K' : K] = [U : U']` is prime to the degree `[L : K] = [U : V]`, then an
element of `A^U` that is a norm from `A^{V'}` is already a norm from `A^V`
(`NormalLayer.mem_normSubgroup_of_coprime`). Indeed, if `x = N_{L'/K'}(y)`, then
`[K' : K] x = N_{K'/K}(x) = N_{L/K}(N_{L'/L}(y))`, while `[L : K] x = N_{L/K}(x)`, and some integer
combination of the two degrees is `1`. So `A^U / N_{L/K}(A^V)` is a quotient of a subgroup of
`A^{U'} / N_{L'/K'}(A^{V'})`, and the order of the first norm quotient divides that of the second
(`NormalLayer.natCard_normQuotient_dvd_of_coprime`).

The base change used in practice is the compositum with the fixed field `E` of an open subgroup
`W`: the layer `LE/KE`, which is `(V ⊓ W) ◁ (U ⊓ W)` (`NormalLayer.compositum`). When `[U : U ⊓ W]`
is prime to `[U : V]`, the compositum has the same degree as the layer
(`NormalLayer.degree_compositum_of_coprime`).

For a formation on an absolute Galois group `G_K` and a prime `p`, adjoining the `p`-th roots of
unity is a step of degree prime to `p`. So a bound `#(A^U / N_{U/V}(A^V)) ∣ p` for the layers of
degree `p` whose ground field contains the `p`-th roots of unity gives the same bound for every
layer of degree `p` (`NormalLayer.natCard_normQuotient_dvd_prime_of_adjoin_nth_roots`). For the
idele-class formation of a number field this is the reduction, in the proof of the second
fundamental inequality for cyclic layers of prime degree, to the case where Kummer theory applies.

## Main definitions

* `TauCeti.ClassFieldTheory.NormalLayer.compositum`: the layer `LE/KE`, that is,
  `(V ⊓ W) ◁ (U ⊓ W)`.

## Main statements

* `TauCeti.ClassFieldTheory.NormalLayer.mem_normSubgroup_of_coprime`: under a base change of
  degree prime to the degree of the layer, an element of the ground level that becomes a norm is
  a norm.
* `TauCeti.ClassFieldTheory.NormalLayer.natCard_normQuotient_dvd_of_coprime`: the order of the
  norm quotient divides that of the base-changed layer.
* `TauCeti.ClassFieldTheory.NormalLayer.degree_compositum_of_coprime`: a compositum of coprime
  degree keeps the degree of the layer.
* `TauCeti.ClassFieldTheory.NormalLayer.natCard_normQuotient_dvd_prime_of_adjoin_nth_roots`: the
  reduction of the bound `#(A^U / N(A^V)) ∣ p` on layers of prime degree `p` to layers whose ground
  field contains the `p`-th roots of unity.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §5 (the proof of the second inequality, reduction
  to the case that the ground field contains the `p`-th roots of unity).
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §4 (proof of Theorem 4.4).
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace NormalLayer

/-! ### Base change of coprime degree -/

section Coprime

variable (F : Formation G) {L L' : NormalLayer G}

/-- **Under a base change of coprime degree, a norm is a norm.** Let `L'/K'` be a layer over the
layer `L/K`, with `K ⊆ K'` and `L ⊆ L'`. If `[K' : K]` is prime to `[L : K]`, an element of the
ground level `A^U` that is a norm from the top level `A^{V'}` of `L'/K'` is a norm from `A^V`. -/
theorem mem_normSubgroup_of_coprime (hg : L'.ground ≤ L.ground) (ht : L'.top ≤ L.top)
    (hcop : (L'.ground.toSubgroup.relIndex L.ground.toSubgroup).Coprime L.degree)
    {x : F.level L.ground} (hx : Submodule.inclusion (F.level_antitone hg) x ∈ L'.normSubgroup F) :
    x ∈ L.normSubgroup F := by
  obtain ⟨y, hy⟩ := (mem_normSubgroup L' F).1 hx
  -- `[K' : K] x = N_{K'/K}(N_{L'/K'} y) = N_{L/K}(N_{L'/L} y)` is a norm.
  have hm : (L'.ground.toSubgroup.relIndex L.ground.toSubgroup) • x ∈ L.normSubgroup F := by
    refine (mem_normSubgroup L F).2 ⟨F.levelNorm ht y, ?_⟩
    have hL := DFunLike.congr_fun (toAddMonoidHom_norm L F) (F.levelNorm ht y)
    have hL' := DFunLike.congr_fun (toAddMonoidHom_norm L' F) y
    simp only [LinearMap.toAddMonoidHom_coe] at hL hL'
    rw [hL, ← AddMonoidHom.comp_apply, ← Formation.levelNorm_trans, ← F.levelNorm_inclusion hg,
      ← hy, hL', ← AddMonoidHom.comp_apply, ← Formation.levelNorm_trans]
  -- `[L : K] x = N_{L/K}(x)` is a norm.
  have hn : L.degree • x ∈ L.normSubgroup F := by
    refine (mem_normSubgroup L F).2
      ⟨Submodule.inclusion (F.level_antitone L.top_le_ground) x, Subtype.ext ?_⟩
    rw [norm_apply_coe_of_mem_level_ground _ _ _ x.2]
    simp
  -- Some integer combination of the two degrees is `1`.
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hx' : x = a • ((L'.ground.toSubgroup.relIndex L.ground.toSubgroup) • x) +
      b • (L.degree • x) := by
    rw [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, hab, one_smul]
  rw [hx']
  exact add_mem (Submodule.smul_mem _ _ hm) (Submodule.smul_mem _ _ hn)

/-- **The norm quotient divides under a base change of coprime degree.** If `L'/K'` lies over the
layer `L/K` and `[K' : K]` is prime to `[L : K]`, the order of `A^U / N_{L/K}(A^V)` divides the
order of `A^{U'} / N_{L'/K'}(A^{V'})`. The first is a quotient of the image of `A^U` in the second.
Both orders are read with `Nat.card`, so the divisibility is vacuous when the second norm quotient
is infinite. -/
theorem natCard_normQuotient_dvd_of_coprime (hg : L'.ground ≤ L.ground) (ht : L'.top ≤ L.top)
    (hcop : (L'.ground.toSubgroup.relIndex L.ground.toSubgroup).Coprime L.degree) :
    Nat.card (L.NormQuotient F) ∣ Nat.card (L'.NormQuotient F) := by
  let φ := L'.normQuotientMk F ∘ₗ Submodule.inclusion (F.level_antitone hg)
  have hker : LinearMap.ker φ ≤ L.normSubgroup F := fun x hx ↦
    mem_normSubgroup_of_coprime F hg ht hcop <| by
      simpa [φ, Submodule.Quotient.mk_eq_zero] using hx
  calc Nat.card (L.NormQuotient F)
      ∣ Nat.card (F.level L.ground ⧸ LinearMap.ker φ) :=
        AddSubgroup.card_dvd_of_surjective (f := (Submodule.factor hker).toAddMonoidHom)
          (Submodule.factor_surjective hker)
    _ ∣ Nat.card (L'.NormQuotient F) :=
        AddSubgroup.card_dvd_of_injective ((LinearMap.ker φ).liftQ φ le_rfl).toAddMonoidHom
          (LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl))

end Coprime

/-! ### The compositum with the fixed field of an open subgroup -/

section Compositum

variable (L : NormalLayer G) (W : OpenSubgroup G)

/-- The **compositum** `LE/KE` of the layer `L/K` with the fixed field `E` of an open subgroup
`W`: the layer `(V ⊓ W) ◁ (U ⊓ W)`. Normality of `V ⊓ W` in `U ⊓ W` comes from that of `V` in `U`
alone; `W` need not be normal. -/
def compositum : NormalLayer G where
  ground := L.ground ⊓ W
  top := L.top ⊓ W
  top_le_ground := inf_le_inf_right W L.top_le_ground
  normal := ⟨fun v hv u ↦ by
    rw [Subgroup.mem_subgroupOf, OpenSubgroup.toSubgroup_inf] at hv ⊢
    exact ⟨L.conj_mem_top (OpenSubgroup.mem_inf.1 u.2).1 hv.1,
      W.toSubgroup.mul_mem (W.toSubgroup.mul_mem (OpenSubgroup.mem_inf.1 u.2).2 hv.2)
        (W.toSubgroup.inv_mem (OpenSubgroup.mem_inf.1 u.2).2)⟩⟩

/-- The ground subgroup of the compositum `LE/KE` is `U ⊓ W`, cutting out `KE`. -/
@[simp]
theorem compositum_ground : (L.compositum W).ground = L.ground ⊓ W :=
  (rfl)

/-- The top subgroup of the compositum `LE/KE` is `V ⊓ W`, cutting out `LE`. -/
@[simp]
theorem compositum_top : (L.compositum W).top = L.top ⊓ W :=
  (rfl)

/-- **A compositum of coprime degree keeps the degree.** If `[U : U ⊓ W]` is prime to the degree
`[U : V]` of the layer, then the compositum `(V ⊓ W) ◁ (U ⊓ W)` has degree `[U : V]` too. -/
theorem degree_compositum_of_coprime
    (hcop : (W.toSubgroup.relIndex L.ground.toSubgroup).Coprime L.degree) :
    (L.compositum W).degree = L.degree := by
  rw [degree_eq_relIndex, degree_eq_relIndex] at *
  simp only [compositum_ground, compositum_top, OpenSubgroup.toSubgroup_inf]
  set U := L.ground.toSubgroup
  set V := L.top.toSubgroup
  have hVU : V ≤ U := OpenSubgroup.toSubgroup_le.2 L.top_le_ground
  have : W.toSubgroup.IsFiniteRelIndex U := Subgroup.isFiniteRelIndex_of_finiteIndex
  have : (V ⊓ W.toSubgroup).IsFiniteRelIndex (U ⊓ W.toSubgroup) :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  -- The tower `V ⊓ W ≤ U ⊓ W ≤ U` and the tower `V ⊓ W ≤ V ≤ U` give
  -- `[U ⊓ W : V ⊓ W] [U : U ⊓ W] = [V : V ⊓ W] [U : V]`.
  have htower : (V ⊓ W.toSubgroup).relIndex (U ⊓ W.toSubgroup) * W.toSubgroup.relIndex U =
      W.toSubgroup.relIndex V * V.relIndex U := by
    rw [← Subgroup.inf_relIndex_right W.toSubgroup U, inf_comm W.toSubgroup U,
      Subgroup.relIndex_mul_relIndex _ _ _ (inf_le_inf_right _ hVU) inf_le_left,
      ← Subgroup.inf_relIndex_right W.toSubgroup V, inf_comm W.toSubgroup V,
      Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left hVU]
  have hmpos : 0 < W.toSubgroup.relIndex U := Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hle : W.toSubgroup.relIndex V ≤ W.toSubgroup.relIndex U :=
    Subgroup.relIndex_le_of_le_right hVU Subgroup.relIndex_ne_zero
  have hapos : 0 < (V ⊓ W.toSubgroup).relIndex (U ⊓ W.toSubgroup) :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  -- `[U : V]` divides `[U ⊓ W : V ⊓ W] [U : U ⊓ W]` and is prime to `[U : U ⊓ W]`, while
  -- `[U ⊓ W : V ⊓ W] ≤ [U : V]` because `[V : V ⊓ W] ≤ [U : U ⊓ W]`.
  have hdvd : V.relIndex U ∣ (V ⊓ W.toSubgroup).relIndex (U ⊓ W.toSubgroup) :=
    hcop.symm.dvd_of_dvd_mul_right ⟨_, htower.trans (mul_comm _ _)⟩
  refine le_antisymm ?_ (Nat.le_of_dvd hapos hdvd)
  refine Nat.le_of_mul_le_mul_right ?_ hmpos
  rw [htower, mul_comm]
  exact Nat.mul_le_mul_left _ hle

/-- **The norm quotient divides that of a compositum of coprime degree.** -/
theorem natCard_normQuotient_dvd_compositum (F : Formation G)
    (hcop : (W.toSubgroup.relIndex L.ground.toSubgroup).Coprime L.degree) :
    Nat.card (L.NormQuotient F) ∣ Nat.card ((L.compositum W).NormQuotient F) := by
  refine natCard_normQuotient_dvd_of_coprime F inf_le_left inf_le_left ?_
  rwa [compositum_ground, OpenSubgroup.toSubgroup_inf, inf_comm, Subgroup.inf_relIndex_right]

end Compositum

/-! ### Adjoining the `p`-th roots of unity -/

section RootsOfUnity

variable {K : Type} [Field K]

/-- **Reduction to a ground field containing the `p`-th roots of unity.** Let `F` be a formation on
the absolute Galois group `G_K` and `p` a prime. If the norm quotient of every layer of degree `p`
whose ground field contains the `p`-th roots of unity has order dividing `p`, then so does the norm
quotient of every layer of degree `p`. The layer `L/K` is replaced by `L(μ_p)/K(μ_p)`: the degree
`[K(μ_p) : K]` is prime to `p`, so this compositum still has degree `p`, and the order of the norm
quotient of `L/K` divides that of `L(μ_p)/K(μ_p)`. -/
theorem natCard_normQuotient_dvd_prime_of_adjoin_nth_roots (F : Formation (AbsoluteGaloisGroup K))
    {p : ℕ} (hp : p.Prime)
    (h : ∀ L' : NormalLayer (AbsoluteGaloisGroup K), L'.degree = p →
      L'.ground.toSubgroup ≤
        (IntermediateField.adjoin K {x : SeparableClosure K | x ^ p = 1}).fixingSubgroup →
      Nat.card (L'.NormQuotient F) ∣ p)
    (L : NormalLayer (AbsoluteGaloisGroup K)) (hL : L.degree = p) :
    Nat.card (L.NormQuotient F) ∣ p := by
  set E := IntermediateField.adjoin K {x : SeparableClosure K | x ^ p = 1}
  -- `E = K(μ_p)` is a finite extension, so `Gal(Kˢ/E)` is open.
  have : Finite {x : SeparableClosure K | x ^ p = 1} := by
    refine (Polynomial.nthRootsFinset p (1 : SeparableClosure K)).finite_toSet.subset fun x hx ↦ ?_
    exact (Polynomial.mem_nthRootsFinset hp.pos 1).2 hx
  have : FiniteDimensional K E :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
  let W : OpenSubgroup (AbsoluteGaloisGroup K) := ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen⟩
  -- `[U : U ⊓ W]` divides `[G_K : W] = [E : K]`, which is prime to `p`.
  have : W.toSubgroup.Normal := by
    -- `W` bundles `E.fixingSubgroup`, so its underlying subgroup is `E.fixingSubgroup` by
    -- definition.
    change E.fixingSubgroup.Normal
    rw [IntermediateField.fixingSubgroup_adjoin_nth_roots_eq_ker]
    infer_instance
  have hcop : (W.toSubgroup.relIndex L.ground.toSubgroup).Coprime L.degree := by
    rw [hL]
    exact (IntermediateField.coprime_index_fixingSubgroup_adjoin_nth_roots hp).coprime_dvd_left
      (Subgroup.relIndex_dvd_index_of_normal _ _)
  refine (natCard_normQuotient_dvd_compositum L W F hcop).trans
    (h _ ((degree_compositum_of_coprime L W hcop).trans hL) ?_)
  rw [compositum_ground, OpenSubgroup.toSubgroup_inf]
  exact inf_le_right

end RootsOfUnity

end NormalLayer

end TauCeti.ClassFieldTheory
