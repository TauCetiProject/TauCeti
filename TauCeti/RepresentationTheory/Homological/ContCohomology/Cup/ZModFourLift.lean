/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Data.ZMod.Four
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialFp
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Character
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Explicit
public import TauCeti.Topology.Algebra.Group.TopologicalAbelianization.Lift

/-!
# Cup squares of classes of `H¹(G, 𝔽₂)` that lift to `ℤ/4`

Let `G` be a topological group and `φ : G →ₜ* ℤ/4` a continuous character. Its reduction modulo
`2` is the continuous character `φ.zmodFourReduction : G → 𝔽₂`, and the class of that character in
`H¹(G, 𝔽₂)` under the identification `TauCeti.cohomFpLinearEquivContinuousZModDual` of
`H¹(G, 𝔽₂)` with the continuous `𝔽₂`-dual of `G` is `φ.zmodFourReductionClass`; it is represented
by the homogeneous cocycle `(g₀, g₁) ↦ φ(g₀⁻¹ g₁) mod 2` (`TauCeti.characterCocycle`). The cup
square of this class vanishes: the carry `ZMod.carryFour = ⌊·/2⌋ : ℤ/4 → 𝔽₂` satisfies
`⌊(u + v)/2⌋ = ⌊u/2⌋ + ⌊v/2⌋ + (u mod 2)(v mod 2)` (`ZMod.carryFour_add`), so the cup square
`(g₀, g₁, g₂) ↦ (φ(g₀⁻¹ g₁) mod 2)(φ(g₁⁻¹ g₂) mod 2)` is the coboundary of the homogeneous
one-cochain `(g₀, g₁) ↦ ⌊φ(g₀⁻¹ g₁)/2⌋`. Conversely, if the cup square of the class of a character
`χ : G → 𝔽₂` vanishes, then the cup cocycle `(g₀, g₁, g₂) ↦ χ(g₀⁻¹ g₁) χ(g₁⁻¹ g₂)` is the coboundary
of a homogeneous one-cochain `ψ`, and `g ↦ χ(g) + 2 ψ(1, g)`, with `χ(g) ∈ {0, 1}` lifted to `ℤ/4`,
is a continuous character `G → ℤ/4` reducing to `χ`: the carry identity makes the two-cocycle
condition on `ψ` exactly the multiplicativity of this lift. Together these are the classical
identification of the cup square on `H¹(G, 𝔽₂)` with the Bockstein of `0 → 𝔽₂ → ℤ/4 → 𝔽₂ → 0`,
whose kernel consists exactly of the classes that lift to `ℤ/4`. The class of a lift is nonzero as
soon as `φ` takes an odd value.

Together with the nonvanishing of the cup square of the generator of `H¹(ℤ/2, 𝔽₂)`, this is what
distinguishes `ℤ/2` from the cyclic groups `ℤ/2ᵏ`, `k ≥ 2`, whose mod-`2` character lifts to
`ℤ/4`: the cup pairing on `H¹(ℤ/2ᵏ, 𝔽₂)` vanishes for `k ≥ 2`.

## Main declarations

* `ContinuousMonoidHom.zmodFourReduction`: the reduction modulo `2` of a continuous character
  `φ : G →ₜ* ℤ/4`, a continuous character `G → 𝔽₂`.
* `ContinuousMonoidHom.zmodFourReductionClass`: the class in `H¹(G, 𝔽₂)` of that reduction;
  `ContinuousMonoidHom.cohomFpLinearEquivContinuousZModDual_zmodFourReductionClass` recovers the
  reduction as its character.
* `ContinuousMonoidHom.zmodFourReductionClass_ne_zero`: the class is nonzero when `φ` takes an
  odd value.
* `ContinuousMonoidHom.cupFp_zmodFourReductionClass_self_eq_zero`: **the cup square of the class
  vanishes**.
* `TauCeti.exists_zmodFourReductionClass_eq_of_cupFp_self_eq_zero`,
  `TauCeti.cupFp_self_eq_zero_iff_exists_zmodFourReductionClass_eq`: **a class of `H¹(G, 𝔽₂)` has
  vanishing cup square exactly when it is the class of the reduction of a character `G → ℤ/4`**.
* `TauCeti.forall_cupFp_self_eq_zero_iff_forall_exists_zmodFourReduction_eq`: every cup square on
  `H¹(G, 𝔽₂)` vanishes exactly when every continuous character `G → 𝔽₂` lifts to `ℤ/4`.
* `TauCeti.forall_exists_zmodFourReduction_eq_iff_of_topologicalAbelianization`: whether every
  continuous character `G → 𝔽₂` lifts to `ℤ/4` is decided on any model of the topological
  abelianization of `G`, since both kinds of characters factor through it.

## References

* J.-P. Serre, *Galois Cohomology*, Springer (1997), Chapter I, §4.5.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  (3.9.10).
-/

public section

namespace TauCeti

open CategoryTheory _root_.ContinuousCohomology TopRep

universe u

-- Preferring the ring path keeps a single additive structure on `ZMod 2`, so that the cochain
-- computations below take place in the additive group the cohomology API expects, as in
-- `TauCeti.Topology.Algebra.Group.Profinite.Demushkin.CyclicTwo`.
attribute [local instance 2000] Ring.toAddCommGroup

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (φ : G →ₜ* Multiplicative (ZMod 4))

/-! ### The reduction modulo `2` and its class -/

omit [IsTopologicalGroup G] in
/-- **The reduction modulo `2` of a continuous character `φ : G →ₜ* ℤ/4`**: the continuous
character `g ↦ φ g mod 2` of `G` with values in `𝔽₂`, as an element of the continuous `𝔽₂`-dual of
`G`. -/
def _root_.ContinuousMonoidHom.zmodFourReduction : continuousZModDual 2 G :=
  Additive.ofMul
    ((⟨(ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)).toAddMonoidHom.toMultiplicative,
      continuous_of_discreteTopology⟩ : Multiplicative (ZMod 4) →ₜ* Multiplicative (ZMod 2)).comp φ)

omit [IsTopologicalGroup G] in
/-- The reduction of `φ` takes the value `φ g mod 2` at `g`. -/
@[simp]
theorem _root_.ContinuousMonoidHom.zmodFourReduction_apply (g : G) :
    Multiplicative.toAdd (Additive.toMul φ.zmodFourReduction g) =
      ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) (Multiplicative.toAdd (φ g)) := by
  rw [_root_.ContinuousMonoidHom.zmodFourReduction]
  rfl

/-- **The class in `H¹(G, 𝔽₂)` of the reduction modulo `2` of a continuous character
`φ : G →ₜ* ℤ/4`**: the class attached to the character `φ.zmodFourReduction` by the identification
`TauCeti.cohomFpLinearEquivContinuousZModDual` of `H¹(G, 𝔽₂)` with the continuous `𝔽₂`-dual of
`G`. -/
noncomputable def _root_.ContinuousMonoidHom.zmodFourReductionClass : cohomFp 2 G 1 :=
  (cohomFpLinearEquivContinuousZModDual 2 G).symm φ.zmodFourReduction

/-- **The character of the class of the reduction of `φ` is the reduction of `φ`.** -/
@[simp]
theorem _root_.ContinuousMonoidHom.cohomFpLinearEquivContinuousZModDual_zmodFourReductionClass :
    cohomFpLinearEquivContinuousZModDual 2 G φ.zmodFourReductionClass = φ.zmodFourReduction :=
  (cohomFpLinearEquivContinuousZModDual 2 G).apply_symm_apply _

omit [IsTopologicalGroup G] in
/-- `φ : G →ₜ* ℤ/4` reduces to the character `χ : G → 𝔽₂` exactly when `φ g mod 2 = χ g` for
every `g`. -/
theorem _root_.ContinuousMonoidHom.zmodFourReduction_eq_iff (χ : continuousZModDual 2 G) :
    φ.zmodFourReduction = χ ↔ ∀ g, ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)
      (Multiplicative.toAdd (φ g)) = Multiplicative.toAdd (Additive.toMul χ g) := by
  refine ⟨fun h g ↦ by rw [← h, φ.zmodFourReduction_apply], fun h ↦ ?_⟩
  apply Additive.toMul.injective
  ext g
  apply Multiplicative.toAdd.injective
  rw [φ.zmodFourReduction_apply, h]

/-- **The class of the reduction of `φ` is nonzero when `φ` takes an odd value**: its character
takes the value `φ g mod 2 ≠ 0` at `g`. -/
theorem _root_.ContinuousMonoidHom.zmodFourReductionClass_ne_zero {g : G}
    (hg : ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) (Multiplicative.toAdd (φ g)) ≠ 0) :
    φ.zmodFourReductionClass ≠ 0 := by
  intro hzero
  have h := φ.zmodFourReduction_apply g
  rw [← φ.cohomFpLinearEquivContinuousZModDual_zmodFourReductionClass, hzero, map_zero] at h
  exact hg (by simpa using h.symm)

/-! ### The cup square -/

/-- The homogeneous one-cochain `(g₀, g₁) ↦ ⌊φ (g₀⁻¹ g₁) / 2⌋` of `G` with trivial `𝔽₂`
coefficients, the carry of `φ`. -/
private noncomputable def carryFourCochain : (homogeneousCochains (trivialFp 2 G)).X 1 :=
  ⟨ContinuousMap.curry ⟨fun q : G × G ↦
      (trivialFpEquiv 2 G).symm (ZMod.carryFour (Multiplicative.toAdd (φ (q.1⁻¹ * q.2)))), by
      have hc : Continuous fun q : G × G ↦ q.1⁻¹ * q.2 := by fun_prop
      exact (continuous_of_discreteTopology (α := Multiplicative (ZMod 4))
        (f := fun z ↦ (trivialFpEquiv 2 G).symm (ZMod.carryFour (Multiplicative.toAdd z)))).comp
          (φ.continuous.comp hc)⟩, fun g ↦ by
    ext h k
    simp only [ContRepresentation.coind₁_apply_apply, trivialFp_ρ_apply_apply,
      ContinuousMap.curry_apply, ContinuousMap.coe_mk]
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]⟩

/-- The value of `carryFourCochain φ` at `(g₀, g₁)` is `⌊φ (g₀⁻¹ g₁) / 2⌋`, lifted into the
coefficient object. -/
-- Not a `simp` lemma: the carrier of the homogeneous cochains is the iterated function space
-- `C(G, C(G, X.V))` only after unfolding the coinduction, which `simp` does not do when matching
-- the left-hand side; use it with `rw`.
private theorem carryFourCochain_apply (g₀ g₁ : G) :
    (carryFourCochain φ).val g₀ g₁ =
      (trivialFpEquiv 2 G).symm (ZMod.carryFour (Multiplicative.toAdd (φ (g₀⁻¹ * g₁)))) :=
  (rfl)

/-- **The cup square of a class of `H¹(G, 𝔽₂)` that lifts to `ℤ/4` vanishes.** The cup square of
the cocycle `(g₀, g₁) ↦ φ (g₀⁻¹ g₁) mod 2` is the coboundary of the homogeneous one-cochain
`(g₀, g₁) ↦ ⌊φ (g₀⁻¹ g₁) / 2⌋`, by the carry identity `ZMod.carryFour_add`. -/
@[simp]
theorem _root_.ContinuousMonoidHom.cupFp_zmodFourReductionClass_self_eq_zero :
    cupFp 2 G φ.zmodFourReductionClass φ.zmodFourReductionClass = 0 := by
  rw [_root_.ContinuousMonoidHom.zmodFourReductionClass,
    cohomFpLinearEquivContinuousZModDual_symm_apply, cupFp_π,
    (homogeneousCochains (trivialFp 2 G)).homologyπ_eq_zero_iff 2 (m := 1)
      (CochainComplex.prev_nat_succ 1)]
  refine ⟨carryFourCochain φ, ?_⟩
  apply (homogeneousCochains (trivialFp 2 G)).iCycles_injective (n := 1 + 1)
  rw [HomologicalComplex.iCycles_toCycles_apply, TopPairing.iCycles_cupCocycles,
    iCycles_characterCocycle]
  apply Subtype.ext
  ext g₀ g₁ g₂
  rw [homogeneousCochains.d_one_apply]
  rw [TopPairing.cupCochain_one_one_apply]
  rw [carryFourCochain_apply, carryFourCochain_apply, carryFourCochain_apply]
  rw [characterCochain_apply, characterCochain_apply]
  rw [fpPairing_bil_apply]
  simp only [LinearEquiv.apply_symm_apply, _root_.ContinuousMonoidHom.zmodFourReduction_apply]
  rw [← map_sub (trivialFpEquiv 2 G).symm, ← map_sub (trivialFpEquiv 2 G).symm]
  have hmul : g₀⁻¹ * g₂ = (g₀⁻¹ * g₁) * (g₁⁻¹ * g₂) := by group
  refine congrArg (trivialFpEquiv 2 G).symm ?_
  -- The identity `carryFour_add` differs from the coboundary equation by a sign, which is
  -- invisible in `𝔽₂`.
  rw [hmul, map_mul φ (g₀⁻¹ * g₁) (g₁⁻¹ * g₂), toAdd_mul,
    ← ZMod.neg_eq_self_mod_two (ZMod.castHom _ (ZMod 2) _ * _), ZMod.carryFour_add]
  abel

/-! ### The converse: a class with vanishing cup square lifts to `ℤ/4` -/

omit φ in
/-- **A class of `H¹(G, 𝔽₂)` with vanishing cup square is the class of the reduction of a
character `G → ℤ/4`.** If the cup square of the class of `χ : G → 𝔽₂` vanishes, its cup cocycle
`(g₀, g₁, g₂) ↦ χ(g₀⁻¹ g₁) χ(g₁⁻¹ g₂)` is the coboundary of a homogeneous one-cochain `ψ`, and
`g ↦ χ(g) + 2 ψ(1, g)` is a continuous character `G → ℤ/4` reducing to `χ`. -/
theorem exists_zmodFourReductionClass_eq_of_cupFp_self_eq_zero {a : cohomFp 2 G 1}
    (h : cupFp 2 G a a = 0) :
    ∃ φ : G →ₜ* Multiplicative (ZMod 4), φ.zmodFourReductionClass = a := by
  set χ := cohomFpLinearEquivContinuousZModDual 2 G a with hχ
  have ha : a = (cohomFpLinearEquivContinuousZModDual 2 G).symm χ :=
    ((cohomFpLinearEquivContinuousZModDual 2 G).symm_apply_apply a).symm
  rw [ha, cohomFpLinearEquivContinuousZModDual_symm_apply, cupFp_π,
    (homogeneousCochains (trivialFp 2 G)).homologyπ_eq_zero_iff 2 (m := 1)
      (CochainComplex.prev_nat_succ 1)] at h
  obtain ⟨b, hb⟩ := h
  have hb' := congrArg ((homogeneousCochains (trivialFp 2 G)).iCycles (1 + 1)) hb
  rw [HomologicalComplex.iCycles_toCycles_apply, TopPairing.iCycles_cupCocycles,
    iCycles_characterCocycle] at hb'
  -- The value of `b` at `(1, g)`, read in `𝔽₂`, and the coboundary equation at `(1, g, g k)`.
  set ψ : G → ZMod 2 := fun g ↦ trivialFpEquiv 2 G (b.val 1 g) with hψdef
  have hψ : ∀ g k : G, ψ k - (ψ (g * k) - ψ g) =
      Multiplicative.toAdd (Additive.toMul χ g) * Multiplicative.toAdd (Additive.toMul χ k) := by
    intro g k
    have h := congrArg (fun z : (homogeneousCochains (trivialFp 2 G)).X (1 + 1) ↦
      trivialFpEquiv 2 G ((z.val : C(G, C(G, C(G, (trivialFp 2 G).V)))) 1 g (g * k))) hb'
    simp only at h
    rw [homogeneousCochains.d_one_apply, TopPairing.cupCochain_one_one_apply,
      characterCochain_apply, characterCochain_apply, fpPairing_bil_apply,
      homogeneousCochains_trivialFp_one_apply_eq 2 b g (g * k), inv_mul_cancel_left, inv_one,
      one_mul, map_sub, map_sub, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply] at h
    simpa [hψdef] using h
  have hχc : Continuous fun g ↦ Multiplicative.toAdd (Additive.toMul χ g) :=
    continuous_toAdd.comp (Additive.toMul χ).continuous
  have hψc : Continuous ψ := continuous_of_discreteTopology.comp (b.val 1).continuous
  have hψ1 : ψ 1 = 0 := by
    have h := hψ 1 1
    rw [one_mul, map_one, toAdd_one, mul_zero] at h
    linear_combination h
  -- The lift `g ↦ χ g + 2 ψ g`, multiplicative by the carry identity.
  let φ : G →ₜ* Multiplicative (ZMod 4) :=
    { toFun := fun g ↦ Multiplicative.ofAdd
        ((ZMod.cast (Multiplicative.toAdd (Additive.toMul χ g)) : ZMod 4) + 2 * ZMod.cast (ψ g))
      map_one' := by simp [hψ1]
      map_mul' := fun g k ↦ by
        have h : ψ (g * k) = ψ g + ψ k -
            Multiplicative.toAdd (Additive.toMul χ g) *
              Multiplicative.toAdd (Additive.toMul χ k) := by
          linear_combination -hψ g k
        rw [← ofAdd_add, h, map_mul, toAdd_mul, ZMod.cast_add_two_mul_cast_sub_mul]
      continuous_toFun := continuous_ofAdd.comp
        ((continuous_of_discreteTopology (f := fun z : ZMod 2 × ZMod 2 ↦
          (ZMod.cast z.1 : ZMod 4) + 2 * ZMod.cast z.2)).comp (hχc.prodMk hψc)) }
  refine ⟨φ, (cohomFpLinearEquivContinuousZModDual 2 G).injective ?_⟩
  rw [φ.cohomFpLinearEquivContinuousZModDual_zmodFourReductionClass, ← hχ,
    φ.zmodFourReduction_eq_iff]
  exact fun g ↦ ZMod.cast_cast_add_two_mul_cast _ _

omit φ in
/-- **Bockstein exactness on `H¹(G, 𝔽₂)`**: a class has vanishing cup square exactly when it is
the class of the reduction modulo `2` of a continuous character `G → ℤ/4`. -/
theorem cupFp_self_eq_zero_iff_exists_zmodFourReductionClass_eq (a : cohomFp 2 G 1) :
    cupFp 2 G a a = 0 ↔ ∃ φ : G →ₜ* Multiplicative (ZMod 4), φ.zmodFourReductionClass = a :=
  ⟨exists_zmodFourReductionClass_eq_of_cupFp_self_eq_zero,
    fun ⟨φ, hφ⟩ ↦ hφ ▸ φ.cupFp_zmodFourReductionClass_self_eq_zero⟩

omit φ in
/-- **Every cup square on `H¹(G, 𝔽₂)` vanishes exactly when every continuous character `G → 𝔽₂`
lifts to a continuous character `G → ℤ/4`.** -/
theorem forall_cupFp_self_eq_zero_iff_forall_exists_zmodFourReduction_eq :
    (∀ a : cohomFp 2 G 1, cupFp 2 G a a = 0) ↔
      ∀ χ : continuousZModDual 2 G, ∃ φ : G →ₜ* Multiplicative (ZMod 4),
        φ.zmodFourReduction = χ := by
  refine ⟨fun h χ ↦ ?_, fun h a ↦ ?_⟩
  · obtain ⟨φ, hφ⟩ := (cupFp_self_eq_zero_iff_exists_zmodFourReductionClass_eq _).1
      (h ((cohomFpLinearEquivContinuousZModDual 2 G).symm χ))
    exact ⟨φ, by rw [← φ.cohomFpLinearEquivContinuousZModDual_zmodFourReductionClass, hφ,
      LinearEquiv.apply_symm_apply]⟩
  · obtain ⟨φ, hφ⟩ := h (cohomFpLinearEquivContinuousZModDual 2 G a)
    rw [cupFp_self_eq_zero_iff_exists_zmodFourReductionClass_eq a]
    exact ⟨φ, (cohomFpLinearEquivContinuousZModDual 2 G).injective (by
      rw [φ.cohomFpLinearEquivContinuousZModDual_zmodFourReductionClass, hφ])⟩

/-! ### Transport of lifting problems along the abelianization -/

omit φ in
/-- **Lifting characters from `𝔽₂` to `ℤ/4` is decided on the abelianization.** For a model
`A ≅ G^{ab}` of the topological abelianization of `G`, every continuous character `G → 𝔽₂` lifts
to a continuous character `G → ℤ/4` exactly when every continuous character `A → 𝔽₂` does: both
kinds of characters factor through `G^{ab}`. -/
theorem forall_exists_zmodFourReduction_eq_iff_of_topologicalAbelianization
    {A : Type*} [Group A] [TopologicalSpace A] (e : TopologicalAbelianization G ≃ₜ* A) :
    (∀ χ : continuousZModDual 2 G, ∃ φ : G →ₜ* Multiplicative (ZMod 4),
        φ.zmodFourReduction = χ) ↔
      ∀ χ : A →ₜ* Multiplicative (ZMod 2), ∃ φ : A →ₜ* Multiplicative (ZMod 4),
        ∀ a, ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) (Multiplicative.toAdd (φ a)) =
          Multiplicative.toAdd (χ a) := by
  -- The projection `G → G^{ab} ≅ A`, kept opaque so that rewriting does not unfold it.
  obtain ⟨π, hπ_apply⟩ : ∃ π : G →ₜ* A, ∀ g, π g = e (g : TopologicalAbelianization G) :=
    ⟨(e : TopologicalAbelianization G →ₜ* A).comp
      (ContinuousMonoidHom.quotientMk (commutator G).topologicalClosure), fun g ↦ rfl⟩
  have hsurj : Function.Surjective π := fun a ↦ by
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e.symm a)
    exact ⟨g, by rw [hπ_apply, hg, ContinuousMulEquiv.apply_symm_apply]⟩
  refine ⟨fun h χ ↦ ?_, fun h χ ↦ ?_⟩
  · obtain ⟨φ, hφ⟩ := h (Additive.ofMul (χ.comp π))
    rw [φ.zmodFourReduction_eq_iff] at hφ
    refine ⟨(TopologicalAbelianization.lift φ).comp (e.symm : A →ₜ* TopologicalAbelianization G),
      fun a ↦ ?_⟩
    obtain ⟨g, rfl⟩ := hsurj a
    rw [ContinuousMonoidHom.coe_comp, Function.comp_apply, hπ_apply,
      ContinuousMonoidHom.coe_coe, ContinuousMulEquiv.symm_apply_apply,
      TopologicalAbelianization.lift_mk, hφ g, toMul_ofMul, ContinuousMonoidHom.coe_comp,
      Function.comp_apply, hπ_apply]
  · obtain ⟨χ', rfl⟩ : ∃ χ' : G →ₜ* Multiplicative (ZMod 2), Additive.ofMul χ' = χ :=
      ⟨Additive.toMul χ, rfl⟩
    obtain ⟨φ, hφ⟩ := h ((TopologicalAbelianization.lift χ').comp
      (e.symm : A →ₜ* TopologicalAbelianization G))
    refine ⟨φ.comp π, (φ.comp π).zmodFourReduction_eq_iff _ |>.2 fun g ↦ ?_⟩
    -- The two sides are compared up to definitional unfolding of `comp` and of the coercions,
    -- because the monoid instance on `Multiplicative (ZMod 2)` produced by
    -- `TopologicalAbelianization.lift` differs syntactically from the quantified one.
    have h₂ : ((TopologicalAbelianization.lift χ').comp
        (e.symm : A →ₜ* TopologicalAbelianization G)) (π g) = χ' g := by
      rw [hπ_apply]
      exact (congrArg (TopologicalAbelianization.lift χ') (e.symm_apply_apply _)).trans
        (TopologicalAbelianization.lift_mk χ' g)
    exact (hφ (π g)).trans (congrArg Multiplicative.toAdd h₂)

end TauCeti
