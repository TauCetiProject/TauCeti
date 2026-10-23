/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.CrossedHom
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicUnits
import Mathlib.NumberTheory.Multiplicity
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Crossed homomorphisms of pro-`p` groups into `ℤ_p` along the lower `p`-series

Let `G` be a topological group, `χ : G →ₜ* ℤ_pˣ` a continuous character with values in the
principal units `1 + pℤ_p` (as every continuous character of a pro-`p` group has,
`TauCeti.IsProP.mem_unitsPrincipal_one`), and `f : G → ℤ_p` a continuous crossed homomorphism for
`χ`, that is `f (g * h) = χ g * f h + f g`. Along the lower `p`-series `λ_k = λ_k(G)` both the
character and the crossed homomorphism gain one power of `p` per step:

* `χ g ≡ 1 mod p ^ (k + 1)` for `g ∈ λ_k` (`TauCeti.mem_unitsPrincipal_of_mem_pLowerCentralSeries`
  in `Profinite/ProP/PadicUnits.lean`), since a `p`-th power of `1 + p ^ (k + 1) ℤ_p` lies in
  `1 + p ^ (k + 2) ℤ_p` and `ℤ_pˣ` is commutative;
* `p ^ k ∣ f g` for `g ∈ λ_k` (`TauCeti.IsCrossedHom.pow_dvd_apply_of_mem_pLowerCentralSeries`),
  since `f (x ^ p) = (1 + χ x + ⋯ + χ x ^ (p - 1)) f x` with the geometric sum divisible by `p`,
  and `f ⁅x, y⁆ = (χ x - 1) f y - (χ y - 1) f x` with `χ x - 1 ∈ p ^ (k + 1) ℤ_p` for `x ∈ λ_k`.

The quotient `f g / p ^ k`, read modulo `p`, is therefore defined on `λ_k`; it is additive, because
`χ ≡ 1 mod p`, and it kills `λ_{k+1}`. It descends to the **graded functional**
`Δ_k(f) : gr_k(G) → 𝔽_p` on the graded piece `gr_k(G) = λ_k ⧸ λ_{k+1}`
(`TauCeti.IsCrossedHom.gradedFunctional`), an `𝔽_p`-linear functional characterized by
`Δ_k(f) (class of g) = (f g / p ^ k) mod p` (`TauCeti.IsCrossedHom.gradedFunctional_gradedMk`). On
the iterated `p`-power `π^k ξ` of the class `ξ ∈ gr_0(G)` of an element `g` on which the character
is trivial, `Δ_k(f) (π^k ξ) = f g mod p`
(`TauCeti.IsCrossedHom.gradedFunctional_gradedPowIter_gradedMkZero`), because `f (g ^ (p ^ k)) =
p ^ k f g` when `χ g = 1`. In degree zero, `Δ_0(f)` is the reduction of `f` modulo `p`, the
`𝔽_p`-character of `G` that `f` induces on the Frattini quotient.

These functionals are the linear maps `Δ` of Labute's Lemma 4. For the crossed homomorphisms `D_i`
of a free pro-`p` group `F` taking the value `1` at the generator `x_i` and `0` at the others,
`Δ_k(D_i)` takes the value `δ_{ij}` on the `p`-power `π^k ξ_j` of the class of a generator `x_j`
on which the character is trivial, and it vanishes on the image of the basis-modification map `δ`
for the orientation of a Demushkin group in normal form. So when a class of a graded piece of the
kernel of the orientation is written as an element of that image plus a combination
`Σ_j c_j π^k ξ_j` of these `p`-powers, as the constrained span statement of the normal form
allows, the `Δ_k(D_i)` read off the coefficients `c_j`. That is what cuts the image of `δ` out of
the graded pieces of the kernel of the orientation in the classification of the dyadic Demushkin
groups of even rank.

## Main definitions

* `TauCeti.IsCrossedHom.gradedFunctional`: the graded functional `Δ_k(f) : gr_k(G) →ₗ[𝔽_p] 𝔽_p`
  of a continuous crossed homomorphism `f` for a character with values in `1 + pℤ_p`.

## Main results

* `TauCeti.IsCrossedHom.pow_dvd_apply_of_mem_pLowerCentralSeries`: a continuous crossed
  homomorphism for such a character is divisible by `p ^ k` on `λ_k(G)`;
  `TauCeti.IsCrossedHom.dvd_apply_of_mem_pLowerCentralSeries_one` is the case `k = 1` for a pro-`p`
  group, the vanishing of `f` modulo `p` on the Frattini subgroup.
* `TauCeti.IsCrossedHom.gradedFunctional_gradedMk`,
  `TauCeti.IsCrossedHom.gradedFunctional_gradedMk_eq_zero_iff`: the defining equation of the graded
  functional, and its kernel on classes.
* `TauCeti.IsCrossedHom.gradedFunctional_gradedMkZero`,
  `TauCeti.IsCrossedHom.gradedFunctional_gradedPowIter_gradedMkZero`: its values in degree zero
  and on the iterated `p`-powers of degree-zero classes.
* `TauCeti.IsCrossedHom.gradedFunctional_gradedPowIterBracket`: its value on the iterated
  `p`-power `π^m [ξ_g, ξ_h]` of a bracket is its value on the bracket itself.
* `TauCeti.IsCrossedHom.map_padicPow_eq_zero_of_eq_zero`,
  `TauCeti.IsCrossedHom.map_padicPow_of_eq_one`: a continuous crossed homomorphism vanishing at `x`
  vanishes on the `p`-adic powers of `x`, and is `ℤ_p`-linear along the `p`-adic powers of an
  element on which the character is trivial.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §4,
  Lemma 4.
* J.-P. Serre, *Galois Cohomology*, Ch. I, §2.3.
-/

public section

namespace TauCeti

open scoped commutatorElement

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the graded
-- functionals below are `ZMod p`-linear maps into `ZMod p` as a module over itself.
attribute [local instance 2000] Ring.toAddCommGroup

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {χ : G →ₜ* ℤ_[p]ˣ}

/-! ### Divisibility of a crossed homomorphism along the lower `p`-series -/

namespace IsCrossedHom

variable {f : G → ℤ_[p]} (hf : IsCrossedHom χ f) (hχ : ∀ g, χ g ∈ unitsPrincipal p 1)
  (hfc : Continuous f)
include hf hχ hfc

/-- **A continuous crossed homomorphism is divisible by `p ^ k` on `λ_k(G)`.** For a continuous
character `χ` with values in `1 + pℤ_p` and a continuous crossed homomorphism `f` for `χ`, the
elements `g` with `p ^ k ∣ f g` form a closed subgroup; it contains the `p`-th powers of the
elements of `λ_{k-1}(G)`, because the geometric sum `1 + χ x + ⋯ + χ x ^ (p - 1)` is divisible by
`p`, and their commutators with `G`, because `χ x - 1 ∈ p ^ k ℤ_p` for `x ∈ λ_{k-1}(G)`. -/
theorem pow_dvd_apply_of_mem_pLowerCentralSeries {k : ℕ} {g : G}
    (hg : g ∈ pLowerCentralSeries p G k) : (p : ℤ_[p]) ^ k ∣ f g := by
  -- The subgroup of the elements on which `f` is divisible by `p ^ k`.
  let S : ℕ → Subgroup G := fun k ↦
    { carrier := {g | (p : ℤ_[p]) ^ k ∣ f g}
      one_mem' := by simp [hf.map_one]
      mul_mem' := fun ha hb ↦ by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [hf.map_mul]
        exact dvd_add (hb.mul_left _) ha
      inv_mem' := fun ha ↦ by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [hf.map_inv]
        exact ha.mul_left _ }
  have hmem : ∀ k g, g ∈ S k ↔ (p : ℤ_[p]) ^ k ∣ f g := fun k g ↦ by
    simp only [S, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq]
  have hS : ∀ k, IsClosed (S k : Set G) := fun k ↦ by
    have : (S k : Set G) = f ⁻¹' (PadicInt.toZModPow k ⁻¹' {0}) := by
      ext g
      rw [Set.mem_preimage, Set.mem_preimage, Set.mem_singleton_iff,
        PadicInt.toZModPow_eq_zero_iff_dvd, SetLike.mem_coe]
      exact hmem k g
    rw [this]
    exact (isClosed_singleton.preimage (PadicInt.continuous_toZModPow k)).preimage hfc
  have hp1 : ∀ x, (p : ℤ_[p]) ∣ (χ x : ℤ_[p]) - 1 := fun x ↦ by
    simpa using mem_unitsPrincipal_iff.1 (hχ x)
  suffices h : ∀ k, pLowerCentralSeries p G k ≤ S k from h k hg
  intro k
  induction k with
  | zero => exact fun g _ ↦ (hmem 0 g).2 (by rw [pow_zero]; exact one_dvd _)
  | succ k ih =>
    rw [pLowerCentralSeries_succ]
    refine (pLowerCentralStep_le_iff (hS (k + 1))).2
      ⟨fun x hx ↦ ?_, Subgroup.commutator_le.2 fun x hx y _ ↦ ?_⟩
    · -- `f (x ^ p) = (1 + χ x + ⋯ + χ x ^ (p - 1)) * f x`, with `p ∣ Σ` and `p ^ k ∣ f x`.
      rw [hmem, hf.map_pow, pow_succ']
      exact mul_dvd_mul (by simpa using dvd_geom_sum₂_self (hp1 x)) ((hmem k x).1 (ih hx))
    · -- `f ⁅x, y⁆ = (χ x - 1) * f y - (χ y - 1) * f x`, with `p ^ (k + 1) ∣ χ x - 1` and
      -- `p ∣ χ y - 1`, `p ^ k ∣ f x`.
      rw [hmem, hf.map_commutatorElement]
      refine dvd_sub ((mem_unitsPrincipal_iff.1
        (mem_unitsPrincipal_of_mem_pLowerCentralSeries hχ hx)).mul_right _) ?_
      rw [pow_succ']
      exact mul_dvd_mul (hp1 y) ((hmem k x).1 (ih hx))

/-! ### The graded functional -/

/-- The quotient `f g / p ^ k` for `g ∈ λ_k(G)`. -/
private noncomputable def gradedQuot (k : ℕ) (g : pLowerCentralSeries p G k) : ℤ_[p] :=
  (dvd_def.1 (hf.pow_dvd_apply_of_mem_pLowerCentralSeries hχ hfc g.2)).choose

private theorem apply_eq_pow_mul_gradedQuot (k : ℕ) (g : pLowerCentralSeries p G k) :
    f g = (p : ℤ_[p]) ^ k * gradedQuot hf hχ hfc k g :=
  (dvd_def.1 (hf.pow_dvd_apply_of_mem_pLowerCentralSeries hχ hfc g.2)).choose_spec

private theorem gradedQuot_eq (k : ℕ) (g : pLowerCentralSeries p G k) {c : ℤ_[p]}
    (hc : f g = (p : ℤ_[p]) ^ k * c) : gradedQuot hf hχ hfc k g = c :=
  mul_left_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))
    ((apply_eq_pow_mul_gradedQuot hf hχ hfc k g).symm.trans hc)

/-- The homomorphism `λ_k(G) → 𝔽_p`, `g ↦ (f g / p ^ k) mod p`, written multiplicatively. -/
private noncomputable def gradedFunctionalAux (k : ℕ) :
    pLowerCentralSeries p G k →* Multiplicative (ZMod p) where
  toFun g := Multiplicative.ofAdd (PadicInt.toZMod (gradedQuot hf hχ hfc k g))
  map_one' := by
    rw [gradedQuot_eq hf hχ hfc k 1 (c := 0) (by rw [OneMemClass.coe_one, hf.map_one, mul_zero]),
      map_zero, ofAdd_zero]
  map_mul' g h := by
    -- `f (g * h) = χ g * f h + f g`, and `χ g ≡ 1 mod p`.
    have hgh : f (g * h : pLowerCentralSeries p G k) =
        (p : ℤ_[p]) ^ k *
          ((χ g : ℤ_[p]) * gradedQuot hf hχ hfc k h + gradedQuot hf hχ hfc k g) := by
      rw [Subgroup.coe_mul, hf.map_mul, apply_eq_pow_mul_gradedQuot hf hχ hfc k h,
        apply_eq_pow_mul_gradedQuot hf hχ hfc k g]
      ring
    rw [gradedQuot_eq hf hχ hfc k _ hgh, map_add, _root_.map_mul,
      mem_unitsPrincipal_one_iff_toZMod.1 (hχ g), one_mul, ofAdd_add, mul_comm]

private theorem gradedFunctionalAux_apply (k : ℕ) (g : pLowerCentralSeries p G k) :
    gradedFunctionalAux hf hχ hfc k g =
      Multiplicative.ofAdd (PadicInt.toZMod (gradedQuot hf hχ hfc k g)) :=
  rfl

private theorem subgroupOf_le_ker_gradedFunctionalAux (k : ℕ) :
    (pLowerCentralSeries p G (k + 1)).subgroupOf (pLowerCentralSeries p G k) ≤
      (gradedFunctionalAux hf hχ hfc k).ker := by
  intro g hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨c, hc⟩ := hf.pow_dvd_apply_of_mem_pLowerCentralSeries hχ hfc hg
  rw [MonoidHom.mem_ker, gradedFunctionalAux_apply,
    gradedQuot_eq hf hχ hfc k g (c := p * c) (by rw [hc, pow_succ]; ring), _root_.map_mul,
    map_natCast, ZMod.natCast_self, zero_mul, ofAdd_zero]

variable (k : ℕ)

/-- **The graded functional of a crossed homomorphism.** For a continuous character `χ` of `G`
with values in `1 + pℤ_p` and a continuous crossed homomorphism `f : G → ℤ_p` for `χ`, the
`𝔽_p`-linear functional `Δ_k(f) : gr_k(G) → 𝔽_p` on the graded piece `gr_k(G) = λ_k ⧸ λ_{k+1}`
sending the class of `g ∈ λ_k(G)` to `(f g / p ^ k) mod p`
(`TauCeti.IsCrossedHom.gradedFunctional_gradedMk`); it is well defined because `f` is divisible by
`p ^ k` on `λ_k(G)` and by `p ^ (k + 1)` on `λ_{k+1}(G)`, and additive because `χ ≡ 1 mod p`. -/
noncomputable def gradedFunctional : gradedPiece p G k →ₗ[ZMod p] ZMod p :=
  (MonoidHom.toAdditiveLeft (QuotientGroup.lift _ (gradedFunctionalAux hf hχ hfc k)
    (subgroupOf_le_ker_gradedFunctionalAux hf hχ hfc k))).toZModLinearMap p

/-- **The graded functional on classes**: if `f g = p ^ k * c` for `g ∈ λ_k(G)`, then
`Δ_k(f) (class of g) = c mod p`. This is the defining equation of
`TauCeti.IsCrossedHom.gradedFunctional`, since `c` is determined by `f g`. -/
theorem gradedFunctional_gradedMk (g : pLowerCentralSeries p G k) {c : ℤ_[p]}
    (hc : f g = (p : ℤ_[p]) ^ k * c) :
    hf.gradedFunctional hχ hfc k (gradedMk p G k g) = PadicInt.toZMod c := by
  rw [gradedFunctional, AddMonoidHom.coe_toZModLinearMap, gradedMk_def,
    MonoidHom.toAdditiveLeft_apply_apply, toMul_ofMul, QuotientGroup.lift_mk,
    gradedFunctionalAux_apply, toAdd_ofAdd, gradedQuot_eq hf hχ hfc k g hc]

/-- **The kernel of the graded functional on classes**: `Δ_k(f)` kills the class of `g ∈ λ_k(G)`
exactly when `p ^ (k + 1) ∣ f g`. -/
@[simp]
theorem gradedFunctional_gradedMk_eq_zero_iff (g : pLowerCentralSeries p G k) :
    hf.gradedFunctional hχ hfc k (gradedMk p G k g) = 0 ↔ (p : ℤ_[p]) ^ (k + 1) ∣ f g := by
  rw [hf.gradedFunctional_gradedMk hχ hfc k g (apply_eq_pow_mul_gradedQuot hf hχ hfc k g),
    PadicInt.toZMod_eq_zero_iff_dvd, apply_eq_pow_mul_gradedQuot hf hχ hfc k g, pow_succ,
    mul_dvd_mul_iff_left (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))]

omit k in
/-- **In degree zero the graded functional is the reduction modulo `p`**:
`Δ_0(f) (class of g) = f g mod p`. -/
@[simp]
theorem gradedFunctional_gradedMkZero (g : G) :
    hf.gradedFunctional hχ hfc 0 (gradedMkZero p G g) = PadicInt.toZMod (f g) := by
  rw [← gradedMk_zero ⟨g, mem_pLowerCentralSeries_zero p g⟩]
  exact hf.gradedFunctional_gradedMk hχ hfc 0 _ (by rw [pow_zero, one_mul])

/-- **The graded functional on an iterated `p`-power.** For `g ∈ G` with `χ g = 1`, the value of
`Δ_k(f)` on `π^k ξ`, where `ξ ∈ gr_0(G)` is the class of `g`, is `f g mod p`: indeed
`f (g ^ (p ^ k)) = p ^ k * f g` when `χ g = 1`. -/
theorem gradedFunctional_gradedPowIter_gradedMkZero {g : G} (hg : χ g = 1) :
    hf.gradedFunctional hχ hfc k (gradedPowIter p G k (gradedMkZero p G g)) =
      PadicInt.toZMod (f g) := by
  rw [gradedPowIter_gradedMkZero]
  exact hf.gradedFunctional_gradedMk hχ hfc k _ (by rw [hf.map_pow_of_eq_one hg, Nat.cast_pow])

/-- **The graded functional on an iterated `p`-power of an element killed by the crossed
homomorphism**: if `f g = 0`, then `Δ_k(f) (π^k ξ) = 0` for the class `ξ` of `g`, since
`f (g ^ (p ^ k))` is a multiple of `f g`. -/
theorem gradedFunctional_gradedPowIter_gradedMkZero_of_eq_zero {g : G} (hg : f g = 0) :
    hf.gradedFunctional hχ hfc k (gradedPowIter p G k (gradedMkZero p G g)) = 0 := by
  rw [gradedPowIter_gradedMkZero, hf.gradedFunctional_gradedMk hχ hfc k _ (c := 0)
    (by rw [hf.map_pow, hg, mul_zero, mul_zero]), map_zero]

omit k in
/-- **The graded functional on an iterated `p`-power of a bracket**:
`Δ_{m+1}(f) (π^m [ξ_g, ξ_h]) = Δ_1(f) ([ξ_g, ξ_h])`, because
`f (⁅g, h⁆ ^ (p ^ m)) = p ^ m * f ⁅g, h⁆`, the character being trivial on commutators. -/
theorem gradedFunctional_gradedPowIterBracket (m : ℕ) (g h : G) :
    hf.gradedFunctional hχ hfc (m + 1) (gradedPowIterBracket p G m g h) =
      hf.gradedFunctional hχ hfc 1
        (gradedBracket p G 0 0 (gradedMkZero p G g) (gradedMkZero p G h)) := by
  have hχ' : χ ⁅g, h⁆ = 1 := by
    rw [_root_.map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.2 (Commute.all _ _)
  obtain ⟨c, hc⟩ := hf.pow_dvd_apply_of_mem_pLowerCentralSeries hχ hfc (k := 1)
    (commutator_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero p g)
      (mem_pLowerCentralSeries_zero p h))
  rw [pow_one] at hc
  rw [gradedPowIterBracket_def, hf.gradedFunctional_gradedMk hχ hfc (m + 1) _ (c := c)
      (by rw [Subgroup.coe_mk, hf.map_pow_of_eq_one hχ', Nat.cast_pow, hc, pow_succ]; ring),
    gradedBracket_gradedMkZero,
    hf.gradedFunctional_gradedMk hχ hfc 1 _ (c := c) (by rw [Subgroup.coe_mk, hc, pow_one])]

end IsCrossedHom

/-- **A continuous crossed homomorphism of a pro-`p` group vanishes modulo `p` on the Frattini
subgroup.** For a continuous character `χ : G → ℤ_pˣ` of a pro-`p` group `G` and a continuous
crossed homomorphism `f` for `χ`, `p ∣ f g` for `g ∈ λ_1(G) = Φ(G)`: the case `k = 1` of
`TauCeti.IsCrossedHom.pow_dvd_apply_of_mem_pLowerCentralSeries`, since `χ ≡ 1 mod p`. -/
theorem IsCrossedHom.dvd_apply_of_mem_pLowerCentralSeries_one (hG : IsProP p G)
    {f : G → ℤ_[p]} (hf : IsCrossedHom χ f) (hfc : Continuous f) {g : G}
    (hg : g ∈ pLowerCentralSeries p G 1) : (p : ℤ_[p]) ∣ f g := by
  simpa using hf.pow_dvd_apply_of_mem_pLowerCentralSeries (hG.mem_unitsPrincipal_one χ) hfc hg

/-! ### Crossed homomorphisms on `p`-adic powers -/

namespace IsCrossedHom

variable [CompactSpace G] [TotallyDisconnectedSpace G] {f : G → ℤ_[p]} (hf : IsCrossedHom χ f)
  (hfc : Continuous f) (hG : IsProP p G)
include hf hfc

/-- **A continuous crossed homomorphism vanishing at `x` vanishes on the `p`-adic powers of
`x`.** -/
theorem map_padicPow_eq_zero_of_eq_zero {x : G} (hx : f x = 0) (l : ℤ_[p]) :
    f (hG.padicPow x l) = 0 := by
  have h : (fun l : ℤ_[p] ↦ f (hG.padicPow x l)) = fun _ ↦ 0 :=
    PadicInt.denseRange_natCast.equalizer
      (hfc.comp (hG.continuous_padicPow.comp (continuous_id.prodMk continuous_const)))
      continuous_const (funext fun k ↦ by
        simp only [Function.comp_apply, hG.padicPow_natCast, hf.map_pow, hx, mul_zero])
  exact congrFun h l

/-- **On an element where the character is trivial, a continuous crossed homomorphism is
`ℤ_p`-linear along `p`-adic powers**: `f (x ^ l) = l * f x` for `l ∈ ℤ_p`. -/
theorem map_padicPow_of_eq_one {x : G} (hx : χ x = 1) (l : ℤ_[p]) :
    f (hG.padicPow x l) = l * f x := by
  have h : (fun l : ℤ_[p] ↦ f (hG.padicPow x l)) = fun l ↦ l * f x :=
    PadicInt.denseRange_natCast.equalizer
      (hfc.comp (hG.continuous_padicPow.comp (continuous_id.prodMk continuous_const)))
      (continuous_id.mul continuous_const) (funext fun k ↦ by
        simp only [Function.comp_apply, hG.padicPow_natCast, hf.map_pow_of_eq_one hx])
  exact congrFun h l

end IsCrossedHom

end TauCeti
