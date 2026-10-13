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

Restriction and corestriction between the layer and its compositum are explicit linear maps
(`NormalLayer.normQuotientRes` and `NormalLayer.normQuotientCor`). Their composite multiplies
by the relative ground index, and restriction is injective at coprime index. When the degrees
agree, `NormalLayer.compositumGalEquiv` bundles the corresponding Galois-group equivalence.

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

/-! ### Galois groups and norm-quotient maps of a compositum -/

/-- The ground subgroup of a compositum is contained in the original ground subgroup. -/
theorem compositum_ground_le : (L.compositum W).ground ≤ L.ground := by
  rw [compositum_ground]
  exact inf_le_left

/-- The top subgroup of a compositum is contained in the original top subgroup. -/
theorem compositum_top_le : (L.compositum W).top ≤ L.top := by
  rw [compositum_top]
  exact inf_le_left

/-- The homomorphism `(U ⊓ W) ⧸ (V ⊓ W) → U ⧸ V` from the Galois group of the base change to that of
the layer, induced by the inclusion `U ⊓ W ≤ U`: in field notation, the restriction
`Gal(LE/KE) → Gal(L/K)`. -/
def compositumGalHom : (L.compositum W).Gal →* L.Gal :=
  @QuotientGroup.quotientMapSubgroupOfOfLe G _ (L.compositum W).top.toSubgroup
    (L.compositum W).ground.toSubgroup L.top.toSubgroup L.ground.toSubgroup
    (L.compositum W).normal L.normal
    (OpenSubgroup.toSubgroup_le.2 (L.compositum_top_le W))
    (OpenSubgroup.toSubgroup_le.2 (L.compositum_ground_le W))

/-- The homomorphism of Galois groups is induced by the inclusion `U ⊓ W ≤ U`. -/
@[simp]
theorem compositumGalHom_mk (u : (L.compositum W).ground) :
    L.compositumGalHom W (QuotientGroup.mk u) =
      QuotientGroup.mk
        (Subgroup.inclusion (OpenSubgroup.toSubgroup_le.2 (L.compositum_ground_le W)) u) :=
  @QuotientGroup.quotientMapSubgroupOfOfLe_mk G _ (L.compositum W).top.toSubgroup
    (L.compositum W).ground.toSubgroup L.top.toSubgroup L.ground.toSubgroup
    (L.compositum W).normal L.normal
    (OpenSubgroup.toSubgroup_le.2 (L.compositum_top_le W))
    (OpenSubgroup.toSubgroup_le.2 (L.compositum_ground_le W)) u

/-- The Galois group of the base change embeds in the Galois group of the layer: an element of
`U ⊓ W` that lies in `V` lies in `V ⊓ W`. -/
theorem compositumGalHom_injective : Function.Injective (L.compositumGalHom W) := by
  refine (injective_iff_map_eq_one _).2 fun γ hγ ↦ ?_
  induction γ using QuotientGroup.induction_on with
  | H u =>
    rw [compositumGalHom_mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hγ
    have hground : (L.compositum W).ground ≤ W := by
      rw [compositum_ground]
      exact inf_le_right
    have hu : (u : G) ∈ W := hground u.2
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, OpenSubgroup.mem_toSubgroup,
      compositum_top, OpenSubgroup.mem_inf]
    exact ⟨hγ, hu⟩

/-- **The degree of the base change divides the degree of the layer.** -/
theorem degree_compositum_dvd : (L.compositum W).degree ∣ L.degree := by
  rw [degree_eq_natCard_gal, degree_eq_natCard_gal]
  exact Subgroup.card_dvd_of_injective _ (L.compositumGalHom_injective W)

/-- When the base change has the same degree as the layer, the homomorphism of Galois groups is
an isomorphism. -/
theorem compositumGalHom_bijective (hdeg : (L.compositum W).degree = L.degree) :
    Function.Bijective (L.compositumGalHom W) :=
  (L.compositumGalHom_injective W).bijective_of_nat_card_le
    (by rw [← degree_eq_natCard_gal, ← degree_eq_natCard_gal, hdeg])

/-- When the compositum has the same degree, restriction is an equivalence of Galois groups. -/
def compositumGalEquiv (hdeg : (L.compositum W).degree = L.degree) :
    (L.compositum W).Gal ≃* L.Gal :=
  MulEquiv.ofBijective (L.compositumGalHom W) (L.compositumGalHom_bijective W hdeg)

/-- The Galois-group equivalence restricts a quotient representative by subgroup inclusion. -/
@[simp]
theorem compositumGalEquiv_mk (hdeg : (L.compositum W).degree = L.degree)
    (u : (L.compositum W).ground) :
    L.compositumGalEquiv W hdeg (QuotientGroup.mk u) =
      QuotientGroup.mk
        (Subgroup.inclusion (OpenSubgroup.toSubgroup_le.2 (L.compositum_ground_le W)) u) :=
  L.compositumGalHom_mk W u

/-! ### Restriction and corestriction of norm quotients -/

variable (F : Formation G)

/-- When the base change has the same degree as the layer, the norm of an element of `A^V` along
the compositum is its norm along the layer: the cosets of `V ⊓ W` in `U ⊓ W` are those of
`V` in `U`. -/
theorem coe_norm_compositum (hdeg : (L.compositum W).degree = L.degree)
    (a : F.level L.top) :
    (dsimp% only ((L.compositum W).norm F
        (Submodule.inclusion (F.level_antitone (L.compositum_top_le W)) a) : F.toRep.V)) =
      L.norm F a := by
  rw [norm_apply_coe, norm_apply_coe]
  refine Fintype.sum_bijective _ (L.compositumGalHom_bijective W hdeg) _ _ fun γ ↦ ?_
  induction γ using QuotientGroup.induction_on with
  | H u =>
    rw [compositumGalHom_mk, rep_ρ_mk_apply_coe, rep_ρ_mk_apply_coe, Submodule.coe_inclusion,
      Subgroup.coe_inclusion]

/-- The **restriction** `A^U / N_{U/V}(A^V) → A^{U ⊓ W} / N_{(U ⊓ W)/(V ⊓ W)}(A^{V ⊓ W})` of norm
quotients to the compositum, induced by the inclusion `A^U ⊆ A^{U ⊓ W}`. It is defined when the
compositum has the same degree as the layer, which makes every norm of the layer a norm of its
compositum. -/
def normQuotientRes (hdeg : (L.compositum W).degree = L.degree) :
    L.NormQuotient F →ₗ[ℤ] (L.compositum W).NormQuotient F :=
  Submodule.mapQ _ _ (Submodule.inclusion (F.level_antitone (L.compositum_ground_le W)))
    fun y hy ↦ by
      obtain ⟨a, rfl⟩ := (L.mem_normSubgroup F).1 hy
      refine Submodule.mem_comap.2 ((mem_normSubgroup _ F).2
        ⟨Submodule.inclusion (F.level_antitone (L.compositum_top_le W)) a, Subtype.ext ?_⟩)
      rw [L.coe_norm_compositum W F hdeg, Submodule.coe_inclusion]

-- `dsimp% only` on the left-hand sides of this and `normQuotientCor_mk`, as explained in the
-- implementation notes of `Formation/Basic.lean`.
/-- Restriction sends the class of `x ∈ A^U` to the class of `x` in `A^{U ⊓ W}`. -/
@[simp]
theorem normQuotientRes_mk (hdeg : (L.compositum W).degree = L.degree)
    (x : F.level L.ground) :
    (dsimp% only (L.normQuotientRes W F hdeg (Submodule.Quotient.mk x))) =
      Submodule.Quotient.mk
        (Submodule.inclusion (F.level_antitone (L.compositum_ground_le W)) x) :=
  (rfl)

/-- The **corestriction** `A^{U ⊓ W} / N_{(U ⊓ W)/(V ⊓ W)}(A^{V ⊓ W}) → A^U / N_{U/V}(A^V)` of norm
quotients from the compositum, induced by `N_{U/(U ⊓ W)} : A^{U ⊓ W} → A^U`, which carries norms
of the compositum to norms of the layer by transitivity of norms. -/
def normQuotientCor : (L.compositum W).NormQuotient F →ₗ[ℤ] L.NormQuotient F :=
  Submodule.mapQ _ _ (F.levelNorm (L.compositum_ground_le W)).toIntLinearMap fun y hy ↦ by
    obtain ⟨b, rfl⟩ := ((L.compositum W).mem_normSubgroup F).1 hy
    refine Submodule.mem_comap.2 ((L.mem_normSubgroup F).2
      ⟨F.levelNorm (L.compositum_top_le W) b, ?_⟩)
    -- Norm transitivity identifies both composites with the norm from `V ⊓ W` to `U`.
    have hL := DFunLike.congr_fun (L.toAddMonoidHom_norm F)
      (F.levelNorm (L.compositum_top_le W) b)
    have hC := DFunLike.congr_fun ((L.compositum W).toAddMonoidHom_norm F) b
    simp only [LinearMap.toAddMonoidHom_coe] at hL hC
    rw [hL, hC, AddMonoidHom.coe_toIntLinearMap, ← AddMonoidHom.comp_apply,
      ← AddMonoidHom.comp_apply, ← Formation.levelNorm_trans, ← Formation.levelNorm_trans]

/-- Corestriction sends the class of `y ∈ A^{U ⊓ W}` to the class of `N_{U/(U ⊓ W)} y`. -/
@[simp]
theorem normQuotientCor_mk (y : F.level (L.compositum W).ground) :
    (dsimp% only (L.normQuotientCor W F (Submodule.Quotient.mk y))) =
      Submodule.Quotient.mk (F.levelNorm (L.compositum_ground_le W) y) :=
  (rfl)

/-- **Corestriction after restriction is multiplication by the index** `[U : U ⊓ W]`. -/
@[simp]
theorem normQuotientCor_normQuotientRes (hdeg : (L.compositum W).degree = L.degree)
    (x : L.NormQuotient F) :
    L.normQuotientCor W F (L.normQuotientRes W F hdeg x) =
      (L.compositum W).ground.toSubgroup.relIndex L.ground.toSubgroup • x := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [normQuotientRes_mk, normQuotientCor_mk, Formation.levelNorm_inclusion,
      Submodule.Quotient.mk_smul]

/-- Restriction to a compositum of coprime index is injective: a class that becomes a norm
already was a norm, by `mem_normSubgroup_of_coprime`. -/
theorem normQuotientRes_injective
    (hcop : (W.toSubgroup.relIndex L.ground.toSubgroup).Coprime L.degree) :
    Function.Injective (L.normQuotientRes W F (L.degree_compositum_of_coprime W hcop)) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [normQuotientRes_mk, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.Quotient.mk_eq_zero]
    exact mem_normSubgroup_of_coprime F (L.compositum_ground_le W) (L.compositum_top_le W)
      (by rwa [compositum_ground, OpenSubgroup.toSubgroup_inf, inf_comm,
        Subgroup.inf_relIndex_right]) hx

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
