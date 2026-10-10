/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Restriction
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.PrimeIndex
public import TauCeti.RepresentationTheory.Homological.TateCohomology.HerbrandQuotient
import TauCeti.RepresentationTheory.Homological.TateCohomology.Periodic

/-!
# `H¹ = 0` and `#H² ∣ [U : V]` from the layers of prime degree

Let `F` be a formation on a profinite group `G` and `V ◁ U` a finite normal layer, `K/F` in field
notation. This file proves that the vanishing of `H¹(U/V, A^V)` and the divisibility
`#H²(U/V, A^V) ∣ [U : V]` follow from the same two statements for the layers `V' ◁ U'` of prime
degree with `U' ≤ U` and `V ≤ V'`, the cyclic extensions of prime degree inside `K/F`
(`NormalLayer.subsingleton_h1_of_prime_degree`,
`NormalLayer.natCard_H2_dvd_degree_of_prime_degree`).
This is the generic finite-group reduction
`TauCeti.groupCohomology.isZero_groupCohomology_one_of_prime_index`, read on the formation: the
subquotient `H/N` of the Galois group `U/V` given by a subgroup `H` and a normal subgroup `N` of `H`
is the Galois group of the layer cut out by the preimages of `N` and `H`, and its action on the
invariants `(A^V)^N` is the coefficient module of that layer.

For a cyclic layer the two statements are equivalent to numerical ones. If the Herbrand quotient
`h(A^V)` of a cyclic layer is its degree `n`, then its norm quotient `A^U / N(A^V)` has at least
`n` elements (`NormalLayer.degree_le_natCard_normQuotient_of_herbrandQuotient_eq`); if moreover the
order of the norm quotient divides `n`, then `H¹` vanishes and `H²` has exactly `n` elements
(`NormalLayer.subsingleton_h1_of_herbrandQuotient_eq_of_natCard_normQuotient_dvd`,
`NormalLayer.natCard_H2_eq_degree_of_herbrandQuotient_eq_of_natCard_normQuotient_dvd`). Together:
if every layer of prime degree inside `K/F` has Herbrand quotient its degree and a norm quotient
whose order divides its degree, then `H¹(U/V, A^V) = 0` and `#H²(U/V, A^V) ∣ [U : V]`
(`NormalLayer.subsingleton_h1_of_herbrandQuotient_of_prime_degree`,
`NormalLayer.natCard_H2_dvd_degree_of_herbrandQuotient_of_prime_degree`).

For the idele classes of a number field these hypotheses are the two fundamental inequalities for
cyclic extensions of prime degree, `h(C_L) = [L : K]` and `[C_K : N_{L/K} C_L] ∣ [L : K]`, and the
conclusions are the vanishing of `H¹(Gal(L/K), C_L)` and the second inequality in its
cohomological form `#H²(Gal(L/K), C_L) ∣ [L : K]` for every finite Galois extension `L/K`.

## Main statements

* `TauCeti.ClassFieldTheory.NormalLayer.subsingleton_h1_of_prime_degree` and
  `natCard_H2_dvd_degree_of_prime_degree`: the reduction to layers of prime degree.
* `TauCeti.ClassFieldTheory.NormalLayer.degree_le_natCard_normQuotient_of_herbrandQuotient_eq`:
  the first inequality for a cyclic layer from its Herbrand quotient.
* `TauCeti.ClassFieldTheory.NormalLayer.subsingleton_h1_of_herbrandQuotient_of_prime_degree` and
  `natCard_H2_dvd_degree_of_herbrandQuotient_of_prime_degree`: the reduction in the numerical form
  of the two inequalities.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §§4–5 (the two inequalities and the
  proof of Theorem 5.1), and Chapter II, §3 (the Herbrand quotient).
-/

public noncomputable section

open CategoryTheory Rep
open _root_.groupCohomology

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace NormalLayer

/-! ### The layer of a subquotient of the Galois group -/

section Subquotient

variable (L : NormalLayer G) {H : Type} [Group H] (f : H →* L.Gal) (N : Subgroup H) [N.Normal]

/-- The layer of the subquotient `H/N` of the Galois group, for `f : H →* U/V`: its ground and
top subgroups are the preimages in `U` of the images of `H` and of `N`. -/
private def subquotientLayer : NormalLayer G where
  ground := ⟨L.subgroupGround f.range,
    Subgroup.isOpen_mono (L.top_le_subgroupGround _) L.top.isOpen⟩
  top := ⟨L.subgroupGround (N.map f),
    Subgroup.isOpen_mono (L.top_le_subgroupGround _) L.top.isOpen⟩
  top_le_ground := OpenSubgroup.toSubgroup_le.1 (L.subgroupGround_mono (Subgroup.map_le_range f N))
  normal := ⟨fun v hv w ↦ by
    obtain ⟨hv', n, hn, hfn⟩ := (L.mem_subgroupGround _).1 (Subgroup.mem_subgroupOf.1 hv)
    obtain ⟨hw', h, hfh⟩ := (L.mem_subgroupGround _).1 w.2
    refine Subgroup.mem_subgroupOf.2 ((L.mem_subgroupGround _).2
      ⟨L.ground.mul_mem (L.ground.mul_mem hw' hv') (L.ground.inv_mem hw'), h * n * h⁻¹,
        (inferInstance : N.Normal).conj_mem n hn h, ?_⟩)
    rw [map_mul, map_mul, map_inv, hfh, hfn]
    rfl⟩

private theorem mem_ground_subquotientLayer {g : G} :
    g ∈ (L.subquotientLayer f N).ground ↔
      ∃ hg : g ∈ L.ground, (QuotientGroup.mk ⟨g, hg⟩ : L.Gal) ∈ f.range :=
  L.mem_subgroupGround f.range

private theorem mem_top_subquotientLayer {g : G} :
    g ∈ (L.subquotientLayer f N).top ↔
      ∃ hg : g ∈ L.ground, (QuotientGroup.mk ⟨g, hg⟩ : L.Gal) ∈ N.map f :=
  L.mem_subgroupGround (N.map f)

private theorem subquotientLayer_ground_le : (L.subquotientLayer f N).ground ≤ L.ground :=
  OpenSubgroup.toSubgroup_le.1 (L.subgroupGround_le_ground f.range)

private theorem le_subquotientLayer_top : L.top ≤ (L.subquotientLayer f N).top :=
  OpenSubgroup.toSubgroup_le.1 (L.top_le_subgroupGround (N.map f))

variable {f}

/-- The homomorphism from the ground subgroup of the layer of `H/N` onto `H/N`: an element is sent
to the class of the element of `H` whose image is its class in `U/V`. -/
private def subquotientGroundHom (hf : Function.Injective f) :
    (L.subquotientLayer f N).ground →* H ⧸ N :=
  (QuotientGroup.mk' N).comp <| (MonoidHom.ofInjective hf).symm.toMonoidHom.comp <|
    ((QuotientGroup.mk' L.relativeTop).comp
      (Subgroup.inclusion (L.subquotientLayer_ground_le f N))).codRestrict f.range
      fun w ↦ ((L.mem_ground_subquotientLayer f N).1 w.2).2

private theorem f_subquotientGroundHom_spec (hf : Function.Injective f)
    (w : (L.subquotientLayer f N).ground) :
    ∃ h : H, f h = QuotientGroup.mk (Subgroup.inclusion (L.subquotientLayer_ground_le f N) w) ∧
      L.subquotientGroundHom N hf w = QuotientGroup.mk h :=
  ⟨_, MonoidHom.apply_ofInjective_symm hf _, rfl⟩

private theorem subquotientGroundHom_surjective (hf : Function.Injective f) :
    Function.Surjective (L.subquotientGroundHom N hf) := by
  intro q
  induction q using QuotientGroup.induction_on with | H h => ?_
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (f h)
  have hw : (u : G) ∈ (L.subquotientLayer f N).ground :=
    (L.mem_ground_subquotientLayer f N).2 ⟨u.2, hu ▸ ⟨h, rfl⟩⟩
  obtain ⟨h', hfh', hq⟩ := L.f_subquotientGroundHom_spec N hf ⟨u, hw⟩
  have hu' : Subgroup.inclusion (L.subquotientLayer_ground_le f N) ⟨u, hw⟩ = u := Subtype.ext rfl
  have hh : h' = h := hf (hfh'.trans ((congrArg QuotientGroup.mk hu').trans hu))
  exact ⟨⟨u, hw⟩, hq.trans (congrArg _ hh)⟩

private theorem ker_subquotientGroundHom (hf : Function.Injective f) :
    (L.subquotientGroundHom N hf).ker = (L.subquotientLayer f N).relativeTop := by
  ext w
  obtain ⟨h, hfh, hq⟩ := L.f_subquotientGroundHom_spec N hf w
  rw [MonoidHom.mem_ker, hq, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    OpenSubgroup.mem_toSubgroup, L.mem_top_subquotientLayer f N]
  constructor
  · intro hn
    exact ⟨L.subquotientLayer_ground_le f N w.2, h, hn, hfh⟩
  · rintro ⟨_, n, hn, hfn⟩
    rwa [← hf (hfn.trans hfh.symm)]

/-- **The Galois group of the layer of `H/N` is `H/N`**, for an injective `f : H →* U/V`. -/
private def subquotientGalEquiv (hf : Function.Injective f) :
    (L.subquotientLayer f N).Gal ≃* H ⧸ N :=
  (QuotientGroup.quotientMulEquivOfEq (L.ker_subquotientGroundHom N hf).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (L.subquotientGroundHom_surjective N hf))

private theorem subquotientGalEquiv_mk (hf : Function.Injective f)
    (w : (L.subquotientLayer f N).ground) :
    L.subquotientGalEquiv N hf (QuotientGroup.mk w) = L.subquotientGroundHom N hf w :=
  (rfl)

private theorem degree_subquotientLayer (hf : Function.Injective f) :
    (L.subquotientLayer f N).degree = N.index := by
  rw [degree_eq_natCard_gal, Nat.card_congr (L.subquotientGalEquiv N hf).toEquiv,
    Subgroup.index]

variable (F : Formation G)

/-- The coefficient module of the layer of `H/N` is the module `(A^V)^N` of invariants of `N`:
both are the elements of the ambient module fixed by the preimage of `N` in `U`. -/
private def subquotientCoeffEquiv :
    F.level (L.subquotientLayer f N).top ≃ₗ[ℤ]
      ((Rep.res f (L.rep F)).quotientToInvariants N).V where
  toFun y := ⟨⟨y, F.level_antitone (L.le_subquotientLayer_top f N) y.2⟩, fun n ↦ by
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (f n)
    have hut : (u : G) ∈ (L.subquotientLayer f N).top :=
      (L.mem_top_subquotientLayer f N).2 ⟨u.2, hu ▸ ⟨n, n.2, rfl⟩⟩
    refine Subtype.ext ?_
    -- `n` acts on `(A^V)^N` as `f n` acts on `A^V`, by definition of `Rep.res` and of
    -- `Representation.quotientToInvariants`
    change ((L.rep F).ρ (f n) _ : F.toRep.V) = y
    rw [← hu]
    exact (F.mem_level.1 y.2) _ hut⟩
  invFun x := ⟨x.1, F.mem_level.2 fun g hg ↦ by
    obtain ⟨hg', n, hn, hfn⟩ := (L.mem_top_subquotientLayer f N).1 hg
    have h := congrArg Subtype.val (x.2 ⟨n, hn⟩)
    -- the invariance of `x` under `n` is its invariance under `f n`, as above
    change ((L.rep F).ρ (f n) x.1 : F.toRep.V) = x.1 at h
    rw [hfn] at h
    exact h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The cohomology of the layer of `H/N` is the cohomology of `H/N` with coefficients in
`(A^V)^N`**, for an injective `f : H →* U/V`. -/
private def subquotientCohomologyIso (hf : Function.Injective f) (n : ℕ) :
    (L.subquotientLayer f N).H F n ≅
      groupCohomology ((Rep.res f (L.rep F)).quotientToInvariants N) n :=
  groupCohomology.mapIso (L.subquotientGalEquiv N hf) (L.subquotientCoeffEquiv N F)
    (fun γ ↦ by
      induction γ using QuotientGroup.induction_on with | H w => ?_
      obtain ⟨h, hfh, hq⟩ := L.f_subquotientGroundHom_spec N hf w
      refine LinearMap.ext fun y ↦ Subtype.ext (Subtype.ext ?_)
      rw [LinearMap.comp_apply, LinearMap.comp_apply, subquotientGalEquiv_mk, hq]
      -- both actions are restrictions of the action on the ambient module: `w` acts on the
      -- level `A^{V'}` through `rep_ρ_mk_apply_coe`, and the class of `h` acts on `(A^V)^N` as
      -- `f h` acts on `A^V`
      change F.toRep.ρ (w : G) (y : F.toRep.V) =
        (((L.rep F).ρ (f h) ⟨y, _⟩ : F.level L.top) : F.toRep.V)
      rw [hfh]
      rfl)
    n

end Subquotient

/-! ### The reduction to layers of prime degree -/

variable (F : Formation G) (L : NormalLayer G)

/-- **`H¹` of a layer vanishes if it vanishes on the layers of prime degree inside it.** If
`H¹(U'/V', A^{V'}) = 0` for every layer `V' ◁ U'` of prime degree with `U' ≤ U` and `V ≤ V'`, then
`H¹(U/V, A^V) = 0`. -/
theorem subsingleton_h1_of_prime_degree
    (h1 : ∀ L' : NormalLayer G, L'.ground ≤ L.ground → L.top ≤ L'.top → L'.degree.Prime →
      Subsingleton (L'.H F 1)) :
    Subsingleton (L.H F 1) :=
  ModuleCat.subsingleton_of_isZero <|
    TauCeti.groupCohomology.isZero_groupCohomology_one_of_prime_index (L.rep F)
      fun _ _ _ _ _ f hf N _ hN ↦
        have := h1 _ (L.subquotientLayer_ground_le f N) (L.le_subquotientLayer_top f N)
          ((L.degree_subquotientLayer N hf).symm ▸ hN)
        (ModuleCat.isZero_of_subsingleton _).of_iso (L.subquotientCohomologyIso N F hf 1).symm

/-- **The order of `H²` of a layer divides its degree if it does on the layers of prime degree
inside it.** If, for every layer `V' ◁ U'` of prime degree with `U' ≤ U` and `V ≤ V'`,
`H¹(U'/V', A^{V'}) = 0` and `#H²(U'/V', A^{V'}) ∣ [U' : V']`, then `#H²(U/V, A^V) ∣ [U : V]`. -/
theorem natCard_H2_dvd_degree_of_prime_degree
    (h1 : ∀ L' : NormalLayer G, L'.ground ≤ L.ground → L.top ≤ L'.top → L'.degree.Prime →
      Subsingleton (L'.H F 1))
    (h2 : ∀ L' : NormalLayer G, L'.ground ≤ L.ground → L.top ≤ L'.top → L'.degree.Prime →
      Nat.card (L'.H F 2) ∣ L'.degree) :
    Nat.card (L.H F 2) ∣ L.degree := by
  rw [degree_eq_natCard_gal]
  refine TauCeti.groupCohomology.natCard_groupCohomology_two_dvd_natCard_of_prime_index (L.rep F)
    (fun _ _ _ _ _ f hf N _ hN ↦ ?_) (fun _ _ _ _ _ f hf N _ hN ↦ ?_)
  · have := h1 _ (L.subquotientLayer_ground_le f N) (L.le_subquotientLayer_top f N)
      ((L.degree_subquotientLayer N hf).symm ▸ hN)
    exact (ModuleCat.isZero_of_subsingleton _).of_iso (L.subquotientCohomologyIso N F hf 1).symm
  · rw [← Nat.card_congr (L.subquotientCohomologyIso N F hf 2).toLinearEquiv.toEquiv,
      ← L.degree_subquotientLayer N hf]
    exact h2 _ (L.subquotientLayer_ground_le f N) (L.le_subquotientLayer_top f N)
      ((L.degree_subquotientLayer N hf).symm ▸ hN)

/-! ### Cyclic layers -/

section Cyclic

variable [IsCyclic L.Gal]

/-- The norm quotient of a cyclic layer has as many elements as its second cohomology:
`A^U / N(A^V) ≃ Ĥ⁰ ≅ Ĥ² ≅ H²`. -/
theorem natCard_normQuotient_eq_natCard_H2 :
    Nat.card (L.NormQuotient F) = Nat.card (L.H F 2) :=
  (Nat.card_congr (L.tateHZeroEquivNormQuotient F).toEquiv).symm.trans <|
    (Rep.FiniteCyclicGroup.natCard_tateCohomology_eq_of_modEq (L.rep F) 0 2 rfl).trans <|
      Nat.card_congr (L.tateHIsoH F 2).toLinearEquiv.toEquiv

/-- In a cyclic layer whose Herbrand quotient is its degree, `#H² = [U : V] · #H¹`, and both groups
are finite. -/
private theorem natCard_H2_eq_degree_mul_of_herbrandQuotient_eq
    (h : TateCohomology.herbrandQuotient (L.rep F) = L.degree) :
    Nat.card (L.H F 2) = L.degree * Nat.card (L.H F 1) ∧ Nat.card (L.H F 1) ≠ 0 := by
  -- `L.H F n` and `groupCohomology.H2`, `H1` are the same `abbrev`s of `groupCohomology`
  have h' : (Nat.card (L.H F 2) : ℚ) / Nat.card (L.H F 1) = L.degree :=
    (TateCohomology.herbrandQuotient_eq_natCard_H2_div_natCard_H1 (L.rep F)).symm.trans h
  -- `Nat.card` of `H¹` is `0` only if `H¹` is infinite, and then the quotient is `0 ≠ [U : V]`
  have h1 : Nat.card (L.H F 1) ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero, div_zero] at h'
    exact L.degree_pos.ne' (by exact_mod_cast h'.symm)
  rw [div_eq_iff (Nat.cast_ne_zero.2 h1)] at h'
  exact ⟨by exact_mod_cast h', h1⟩

/-- **The first inequality from the Herbrand quotient.** If the Herbrand quotient `h(A^V)` of a
cyclic layer is its degree, then its norm quotient `A^U / N(A^V)` has at least `[U : V]` elements.
-/
theorem degree_le_natCard_normQuotient_of_herbrandQuotient_eq
    (h : TateCohomology.herbrandQuotient (L.rep F) = L.degree) :
    L.degree ≤ Nat.card (L.NormQuotient F) := by
  obtain ⟨h2, h1⟩ := L.natCard_H2_eq_degree_mul_of_herbrandQuotient_eq F h
  rw [L.natCard_normQuotient_eq_natCard_H2 F, h2]
  exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h1)

/-- **`H¹` of a cyclic layer from the two inequalities.** If the Herbrand quotient of a cyclic layer
is its degree and the order of its norm quotient divides its degree, then `H¹(U/V, A^V) = 0`. -/
theorem subsingleton_h1_of_herbrandQuotient_eq_of_natCard_normQuotient_dvd
    (h : TateCohomology.herbrandQuotient (L.rep F) = L.degree)
    (hN : Nat.card (L.NormQuotient F) ∣ L.degree) :
    Subsingleton (L.H F 1) := by
  obtain ⟨h2, h1⟩ := L.natCard_H2_eq_degree_mul_of_herbrandQuotient_eq F h
  rw [L.natCard_normQuotient_eq_natCard_H2 F, h2] at hN
  refine (Nat.card_eq_one_iff_unique.1 ?_).1
  have := Nat.le_of_dvd L.degree_pos hN
  have := Nat.pos_of_ne_zero h1
  nlinarith [L.degree_pos]

/-- **`H²` of a cyclic layer from the two inequalities.** If the Herbrand quotient of a cyclic layer
is its degree and the order of its norm quotient divides its degree, then `H²(U/V, A^V)` has
exactly `[U : V]` elements. -/
theorem natCard_H2_eq_degree_of_herbrandQuotient_eq_of_natCard_normQuotient_dvd
    (h : TateCohomology.herbrandQuotient (L.rep F) = L.degree)
    (hN : Nat.card (L.NormQuotient F) ∣ L.degree) :
    Nat.card (L.H F 2) = L.degree := by
  have := L.subsingleton_h1_of_herbrandQuotient_eq_of_natCard_normQuotient_dvd F h hN
  rw [(L.natCard_H2_eq_degree_mul_of_herbrandQuotient_eq F h).1, Nat.card_of_subsingleton 0,
    mul_one]

end Cyclic

/-! ### The reduction in terms of the two inequalities -/

/-- A layer of prime degree has a cyclic Galois group. -/
private theorem isCyclic_gal_of_prime_degree {L : NormalLayer G} (hp : L.degree.Prime) :
    IsCyclic L.Gal :=
  have : Fact (Nat.card L.Gal).Prime := ⟨L.degree_eq_natCard_gal ▸ hp⟩
  isCyclic_of_prime_card rfl

/-- **`H¹` of a layer vanishes if the two inequalities hold for the layers of prime degree inside
it.** If every layer `V' ◁ U'` of prime degree with `U' ≤ U` and `V ≤ V'` has Herbrand quotient its
degree and a norm quotient whose order divides its degree, then `H¹(U/V, A^V) = 0`. -/
theorem subsingleton_h1_of_herbrandQuotient_of_prime_degree
    (h : ∀ L' : NormalLayer G, L'.ground ≤ L.ground → L.top ≤ L'.top → L'.degree.Prime →
      TateCohomology.herbrandQuotient (L'.rep F) = L'.degree ∧
        Nat.card (L'.NormQuotient F) ∣ L'.degree) :
    Subsingleton (L.H F 1) :=
  L.subsingleton_h1_of_prime_degree F fun L' hU hV hp ↦
    have := isCyclic_gal_of_prime_degree hp
    L'.subsingleton_h1_of_herbrandQuotient_eq_of_natCard_normQuotient_dvd F
      (h L' hU hV hp).1 (h L' hU hV hp).2

/-- **The order of `H²` of a layer divides its degree if the two inequalities hold for the layers
of prime degree inside it.** If every layer `V' ◁ U'` of prime degree with `U' ≤ U` and `V ≤ V'` has
Herbrand quotient its degree and a norm quotient whose order divides its degree, then
`#H²(U/V, A^V) ∣ [U : V]`. -/
theorem natCard_H2_dvd_degree_of_herbrandQuotient_of_prime_degree
    (h : ∀ L' : NormalLayer G, L'.ground ≤ L.ground → L.top ≤ L'.top → L'.degree.Prime →
      TateCohomology.herbrandQuotient (L'.rep F) = L'.degree ∧
        Nat.card (L'.NormQuotient F) ∣ L'.degree) :
    Nat.card (L.H F 2) ∣ L.degree :=
  L.natCard_H2_dvd_degree_of_prime_degree F
    (fun L' hU hV hp ↦
      have := isCyclic_gal_of_prime_degree hp
      L'.subsingleton_h1_of_herbrandQuotient_eq_of_natCard_normQuotient_dvd F
        (h L' hU hV hp).1 (h L' hU hV hp).2)
    fun L' hU hV hp ↦
      have := isCyclic_gal_of_prime_degree hp
      (L'.natCard_H2_eq_degree_of_herbrandQuotient_eq_of_natCard_normQuotient_dvd F
        (h L' hU hV hp).1 (h L' hU hV hp).2).dvd

end NormalLayer

end TauCeti.ClassFieldTheory
