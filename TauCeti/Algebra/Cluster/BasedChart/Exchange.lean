/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Finsupp
public import TauCeti.Algebra.Cluster.BasedChart.Subalgebra
public import TauCeti.Algebra.Cluster.OneExchange.Independence

/-!
# One exchange of a based chart

Let `M` be a based chart for `(R, u, Λ)` in an `R`-algebra `B`, with exponents `I →₀ ℤ`, and
fix a direction `k`. The monomials whose exponent vanishes at `k` span a subalgebra `C`, and
the coordinate `x = M(e_k)` has unique left coefficients in `C` for its integer powers. A unit
`y` with `y * x ∈ C`, quasi-commuting with every monomial of `C` according to an alternating
form `Λ'` that agrees with `Λ` off `k`, then defines a new based chart for `(R, u, Λ')`:

`M'(a) = u ^ (-(a_k * Λ'(e_k, a°))) * y ^ a_k * M(a°)`, where `a° = a - a_k e_k`.

No hypothesis on the old form `Λ` is needed: it enters only through its values on exponents
vanishing at `k`, where it agrees with `Λ'`. The new chart has coordinate `y` in direction `k`,
keeps the other coordinates of `M`, and has the same subalgebra `C`. The exchange element
`E = y * x` normalizes `C` by `TauCeti.BasedChart.mul_monomial_mul_mul_inv_mem_subalgebra_iff`,
and `y = E * x⁻¹` is a skew exchange in the sense of `TauCeti.linearIndependent_mul_inv_zpow`.
Neither the multiplication rule nor faithfulness of the new chart is assumed, and the ambient
algebra need not be a division ring; this is the chart a seed mutation produces from an
invertible exchange element.

Faithfulness passes between scalar rings in both directions. Tau Ceti's
`LinearIndependent.of_smul_of_span_eq_top`, through
`TauCeti.BasedChart.linearIndependent_zpow_monomial`, turns independence of the monomials of
`M` over `R` into unique left coefficients in `C` for the powers of `x`. After the skew
exchange gives the same for the powers of `y`, Mathlib's `linearIndependent_smul` combines
them with the independence of the monomials of `C` into independence of the new monomials
over `R`.

When the cross terms are given as an additive map `l` on the exponents vanishing at `k` in
place of `Λ'`, `LinearMap.BilinForm.exchange Λ k l` is the exchanged bilinear form
`Λ'(a, b) = Λ(a°, b°) + a_k * l(b°) - b_k * l(a°)`. It is alternating when `Λ` vanishes on the
diagonal of these exponents, in particular when `Λ` is alternating, and it is the only
alternating form with this restriction and these cross terms. `BasedChart.exchangeOfDual` is
the exchanged chart for it.

## Main definitions

* `TauCeti.BasedChart.exchange`: the based chart obtained by exchanging the `k`th coordinate.
* `LinearMap.BilinForm.exchange`: the exchanged bilinear form, built from `Λ` and the cross
  terms `l`; it is alternating when `Λ` is.
* `TauCeti.BasedChart.exchangeOfDual`: the exchanged chart for this form.

## Main results

* `TauCeti.BasedChart.eq_exchange`: the exchanged chart is the only chart for `Λ'` with these
  coordinates; `TauCeti.BasedChart.eq_exchangeOfDual` is the same for the chart built from `l`.
* `TauCeti.BasedChart.subalgebra_exchange`: the exchanged chart keeps the subalgebra of every
  set of exponents vanishing at `k`.
* `LinearMap.BilinForm.IsAlt.apply_eq_erase`: an alternating form on `I →₀ R`, expanded along
  the `k`th coordinate.
* `LinearMap.BilinForm.IsAlt.eq_exchange`: an alternating form is determined by its
  restriction to the exponents vanishing at `k` and its cross terms.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics
  195 (2005), §4 and Lemmas 5.5–5.6, for toric frames and quantum exchange.
* A. Berenstein, S. Fomin and A. Zelevinsky, *Cluster algebras III: Upper bounds and
  double Bruhat cells*, Duke Mathematical Journal 126 (2005), Lemmas 4.1–4.2,
  for the commutative exchange.
-/

public section

namespace LinearMap.BilinForm

variable {I : Type*}

/-- The exchanged bilinear form in direction `k` with cross terms `l`, an additive map on the
exponents vanishing at `k`: it agrees with `Λ` on these exponents and pairs `e_k` with them by
`l`, namely `Λ'(a, b) = Λ(a°, b°) + a_k * l(b°) - b_k * l(a°)` with `a° = a - a_k e_k`. -/
noncomputable def exchange (Λ : LinearMap.BilinForm ℤ (I →₀ ℤ)) (k : I)
    (l : Module.Dual ℤ (Finsupp.applyAddHom (M := ℤ) k).ker) : LinearMap.BilinForm ℤ (I →₀ ℤ) :=
  let l' := l ∘ₗ ((Finsupp.eraseAddHom (M := ℤ) k).codRestrict _ fun _ ↦
    AddMonoidHom.mem_ker.mpr Finsupp.erase_same).toIntLinearMap
  Λ.compl₁₂ (Finsupp.eraseAddHom k).toIntLinearMap (Finsupp.eraseAddHom k).toIntLinearMap +
    (Finsupp.lapply k).smulRight l' - ((Finsupp.lapply k).smulRight l').flip

/-- The exchanged form is `Λ'(a, b) = Λ(a°, b°) + a_k * l(b°) - b_k * l(a°)`. -/
theorem exchange_apply (Λ : LinearMap.BilinForm ℤ (I →₀ ℤ)) (k : I)
    (l : Module.Dual ℤ (Finsupp.applyAddHom (M := ℤ) k).ker) (a b : I →₀ ℤ) :
    Λ.exchange k l a b = Λ (a.erase k) (b.erase k) +
      a k * l ⟨b.erase k, AddMonoidHom.mem_ker.mpr Finsupp.erase_same⟩ -
        b k * l ⟨a.erase k, AddMonoidHom.mem_ker.mpr Finsupp.erase_same⟩ := by
  simp [exchange]

/-- The exchanged form is alternating when `Λ` vanishes on the diagonal of the exponents
vanishing at `k`, in particular when `Λ` is alternating. -/
theorem isAlt_exchange {Λ : LinearMap.BilinForm ℤ (I →₀ ℤ)} (k : I)
    (hΛ : ∀ a : I →₀ ℤ, a k = 0 → Λ a a = 0)
    (l : Module.Dual ℤ (Finsupp.applyAddHom (M := ℤ) k).ker) : (Λ.exchange k l).IsAlt :=
  fun a ↦ by rw [exchange_apply, hΛ _ Finsupp.erase_same, zero_add, sub_self]

/-- The exchanged form agrees with `Λ` on exponents vanishing at `k`. -/
@[simp]
theorem exchange_apply_of_apply_eq_zero (Λ : LinearMap.BilinForm ℤ (I →₀ ℤ)) {k : I}
    (l : Module.Dual ℤ (Finsupp.applyAddHom (M := ℤ) k).ker) {a b : I →₀ ℤ} (ha : a k = 0)
    (hb : b k = 0) : Λ.exchange k l a b = Λ a b := by
  rw [exchange_apply, ha, hb, zero_mul, zero_mul, add_zero, sub_zero,
    Finsupp.erase_of_notMem_support (Finsupp.notMem_support_iff.mpr ha),
    Finsupp.erase_of_notMem_support (Finsupp.notMem_support_iff.mpr hb)]

/-- The exchanged form pairs `e_k` with `b` by `l(b°)`. -/
@[simp]
theorem exchange_single_self_apply (Λ : LinearMap.BilinForm ℤ (I →₀ ℤ)) (k : I)
    (l : Module.Dual ℤ (Finsupp.applyAddHom (M := ℤ) k).ker) (b : I →₀ ℤ) :
    Λ.exchange k l (Finsupp.single k 1) b =
      l ⟨b.erase k, AddMonoidHom.mem_ker.mpr Finsupp.erase_same⟩ := by
  simp only [exchange_apply, Finsupp.erase_single, Finsupp.single_eq_same, one_mul, map_zero]
  rw [LinearMap.zero_apply, zero_add, sub_eq_self, mul_eq_zero]
  exact Or.inr (map_zero l)

/-- An alternating form that agrees with `Λ` on the exponents vanishing at `k` and pairs `e_k`
with them by `l` is the exchanged form `Λ.exchange k l`. -/
theorem IsAlt.eq_exchange {Λ Λ' : LinearMap.BilinForm ℤ (I →₀ ℤ)} (hΛ' : Λ'.IsAlt) {k : I}
    {l : Module.Dual ℤ (Finsupp.applyAddHom (M := ℤ) k).ker}
    (hΛΛ' : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 → Λ' a b = Λ a b)
    (hl : ∀ b : (Finsupp.applyAddHom (M := ℤ) k).ker, Λ' (Finsupp.single k 1) b = l b) :
    Λ' = Λ.exchange k l :=
  LinearMap.BilinForm.ext fun a b ↦ by
    rw [hΛ'.apply_eq_erase k, exchange_apply, hΛΛ' _ _ Finsupp.erase_same Finsupp.erase_same,
      ← hl, ← hl]

end LinearMap.BilinForm

namespace TauCeti

namespace BasedChart

section Exchange

variable {R I B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]
  {u : Rˣ} {Λ Λ' : LinearMap.BilinForm ℤ (I →₀ ℤ)}

/-- Scalar actions by integer powers of `u` compose by adding the exponents. -/
private theorem val_zpow_smul_val_zpow_smul (m n : ℤ) (x : B) :
    ((u ^ m : Rˣ) : R) • ((u ^ n : Rˣ) : R) • x = ((u ^ (m + n) : Rˣ) : R) • x := by
  rw [smul_smul, ← Units.val_mul, ← zpow_add]

/-- The quasi-commutation of `y` with the other-coordinate monomials, for integer powers. -/
private theorem val_zpow_mul_monomial (M : BasedChart u Λ B) (k : I) {y : Bˣ}
    (hy : ∀ a : I →₀ ℤ, a k = 0 → y * M.monomial a =
      Units.map (algebraMap R B) (u ^ (2 * Λ' (Finsupp.single k 1) a)) * (M.monomial a * y))
    {a : I →₀ ℤ} (ha : a k = 0) (n : ℤ) :
    ((y ^ n : Bˣ) : B) * M.monomial a =
      ((u ^ (n * (2 * Λ' (Finsupp.single k 1) a)) : Rˣ) : R) • ((M.monomial a : B) * ↑(y ^ n)) := by
  -- Scalar units are central, so `M(a)` semiconjugates `c * y` to `y`, and hence their powers.
  have hc (r : Rˣ) (g : Bˣ) : Commute (Units.map (algebraMap R B : R →* B) r) g :=
    Units.ext (Algebra.commutes (r : R) (g : B))
  set c := Units.map (algebraMap R B : R →* B) (u ^ (2 * Λ' (Finsupp.single k 1) a))
  have hs : SemiconjBy (M.monomial a) (c * y) y := by
    rw [SemiconjBy, hy a ha, ← mul_assoc, ← (hc _ _).eq, mul_assoc]
  have h := hs.zpow_right n
  rw [SemiconjBy, (hc _ y).mul_zpow] at h
  have h' : y ^ n * M.monomial a = c ^ n * (M.monomial a * y ^ n) := by
    rw [← h, ← mul_assoc, ← mul_assoc, ((hc _ _).zpow_left n).eq]
  rw [← map_zpow, ← zpow_mul, mul_comm (2 * _) n] at h'
  simpa [Algebra.smul_def, -map_zpow] using congrArg Units.val h'

/-- The monomials of the exchanged chart, before their chart laws are proved. -/
private noncomputable def exchangeMonomial (M : BasedChart u Λ B) (k : I)
    (Λ' : LinearMap.BilinForm ℤ (I →₀ ℤ)) (y : Bˣ) (a : I →₀ ℤ) : Bˣ :=
  Units.map (algebraMap R B) (u ^ (-(a k * Λ' (Finsupp.single k 1) (a.erase k)))) *
    y ^ a k * M.monomial (a.erase k)

/-- The exchanged monomials as scalar multiples in the ambient algebra. -/
private theorem val_exchangeMonomial (M : BasedChart u Λ B) (k : I)
    (Λ' : LinearMap.BilinForm ℤ (I →₀ ℤ)) (y : Bˣ) (a : I →₀ ℤ) :
    (exchangeMonomial M k Λ' y a : B) =
      ((u ^ (-(a k * Λ' (Finsupp.single k 1) (a.erase k))) : Rˣ) : R) •
        (((y ^ a k : Bˣ) : B) * M.monomial (a.erase k)) := by
  simp [exchangeMonomial, Algebra.smul_def, mul_assoc, -map_zpow]

/-- The exchanged monomials satisfy the normalized multiplication rule for `Λ'`. -/
private theorem exchangeMonomial_mul (M : BasedChart u Λ B) (k : I) (hΛ' : Λ'.IsAlt)
    (hΛΛ' : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 → Λ' a b = Λ a b) {y : Bˣ}
    (hy : ∀ a : I →₀ ℤ, a k = 0 → y * M.monomial a =
      Units.map (algebraMap R B) (u ^ (2 * Λ' (Finsupp.single k 1) a)) * (M.monomial a * y))
    (a b : I →₀ ℤ) :
    exchangeMonomial M k Λ' y a * exchangeMonomial M k Λ' y b =
      Units.map (algebraMap R B) (u ^ Λ' a b) * exchangeMonomial M k Λ' y (a + b) := by
  apply Units.ext
  have hswap : (M.monomial (a.erase k) : B) * ↑(y ^ b k) =
      ((u ^ (-(b k * (2 * Λ' (Finsupp.single k 1) (a.erase k)))) : Rˣ) : R) •
        (((y ^ b k : Bˣ) : B) * M.monomial (a.erase k)) := by
    rw [val_zpow_mul_monomial M k hy Finsupp.erase_same, val_zpow_smul_val_zpow_smul,
      neg_add_cancel, zpow_zero, Units.val_one, one_smul]
  have hprod : (((y ^ a k : Bˣ) : B) * M.monomial (a.erase k)) *
      (((y ^ b k : Bˣ) : B) * M.monomial (b.erase k)) =
      ((u ^ (-(b k * (2 * Λ' (Finsupp.single k 1) (a.erase k)))) : Rˣ) : R) •
        ((u ^ (Λ (a.erase k) (b.erase k)) : Rˣ) : R) •
          (((y ^ (a + b) k : Bˣ) : B) * M.monomial ((a + b).erase k)) := by
    calc (((y ^ a k : Bˣ) : B) * M.monomial (a.erase k)) *
          (((y ^ b k : Bˣ) : B) * M.monomial (b.erase k))
        = ((y ^ a k : Bˣ) : B) * ((M.monomial (a.erase k) : B) * ↑(y ^ b k)) *
            M.monomial (b.erase k) := by simp only [mul_assoc]
      _ = ((y ^ a k : Bˣ) : B) *
            (((u ^ (-(b k * (2 * Λ' (Finsupp.single k 1) (a.erase k)))) : Rˣ) : R) •
              (((y ^ b k : Bˣ) : B) * M.monomial (a.erase k))) * M.monomial (b.erase k) := by
        rw [hswap]
      _ = ((u ^ (-(b k * (2 * Λ' (Finsupp.single k 1) (a.erase k)))) : Rˣ) : R) •
            ((((y ^ a k : Bˣ) : B) * ↑(y ^ b k)) *
              ((M.monomial (a.erase k) : B) * M.monomial (b.erase k))) := by
        simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
      _ = _ := by
        rw [← Units.val_mul, ← zpow_add, val_monomial_mul, mul_smul_comm, Finsupp.erase_add,
          Finsupp.add_apply]
  -- The exponents of `u` on the two sides agree after expanding `Λ' a b` along `e_k`.
  have hexp : -(a k * Λ' (Finsupp.single k 1) (a.erase k)) +
        -(b k * Λ' (Finsupp.single k 1) (b.erase k)) +
        (-(b k * (2 * Λ' (Finsupp.single k 1) (a.erase k))) + Λ (a.erase k) (b.erase k)) =
      Λ' a b + -((a + b) k * Λ' (Finsupp.single k 1) ((a + b).erase k)) := by
    rw [hΛ'.apply_eq_erase k a b, hΛΛ' _ _ Finsupp.erase_same Finsupp.erase_same,
      Finsupp.erase_add, Finsupp.add_apply, map_add]
    ring
  rw [Units.val_mul, Units.val_mul, val_exchangeMonomial, val_exchangeMonomial,
    val_exchangeMonomial, smul_mul_smul_comm, hprod, Units.coe_map, MonoidHom.coe_ofClass,
    ← Algebra.smul_def, ← Units.val_mul, ← zpow_add]
  simp only [val_zpow_smul_val_zpow_smul]
  exact congrArg (fun n : ℤ ↦ ((u ^ n : Rˣ) : R) • _) hexp

/-- The exchanged monomials are linearly independent over `R`. -/
private theorem linearIndependent_exchangeMonomial (M : BasedChart u Λ B) (k : I) {y : Bˣ}
    (hy : ∀ a : I →₀ ℤ, a k = 0 → y * M.monomial a =
      Units.map (algebraMap R B) (u ^ (2 * Λ' (Finsupp.single k 1) a)) * (M.monomial a * y))
    (hyx : ((y * M.monomial (Finsupp.single k 1) : Bˣ) : B) ∈
      M.subalgebra (Finsupp.applyAddHom k).ker) :
    LinearIndependent R fun a ↦ (exchangeMonomial M k Λ' y a : B) := by
  set N : AddSubgroup (I →₀ ℤ) := (Finsupp.applyAddHom k).ker with hN_def
  have hN {a : I →₀ ℤ} : a ∈ N ↔ a k = 0 := by simp [hN_def]
  -- Powers of the old coordinate, then of `y`, have unique left coefficients in `C`.
  have hx := M.linearIndependent_zpow_monomial (N := N)
    (e := Finsupp.single k 1) fun n hn ↦ by simpa using hN.mp hn
  have hyC := linearIndependent_mul_inv_zpow _ _ _
    (fun _ ↦ M.monomial_inv_mul_mul_mem_subalgebra (Finsupp.single k 1)) hyx hx
  simp only [mul_inv_cancel_right] at hyC
  -- Hence the products `M(a°) * y ^ n` are independent over `R`.
  have hb : LinearIndependent R fun a : N ↦
      (⟨M.monomial (a : I →₀ ℤ), M.monomial_mem_subalgebra a.property⟩ :
        M.subalgebra N) := by
    apply LinearIndependent.of_comp (M.subalgebra _).val.toLinearMap
    exact M.linearIndependent.comp _ Subtype.val_injective
  have hinj : Function.Injective fun a : I →₀ ℤ ↦
      ((⟨a.erase k, hN.mpr Finsupp.erase_same⟩ : N), a k) := by
    intro a b h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    rw [← Finsupp.single_add_erase k a, ← Finsupp.single_add_erase k b, h.1, h.2]
  convert ((linearIndependent_smul hb hyC).comp _ hinj).units_smul
    (fun a ↦ u ^ (a k * Λ' (Finsupp.single k 1) (a.erase k))) using 1
  funext a
  rw [val_exchangeMonomial, val_zpow_mul_monomial M k hy Finsupp.erase_same,
    val_zpow_smul_val_zpow_smul, show -(a k * Λ' (Finsupp.single k 1) (a.erase k)) +
      a k * (2 * Λ' (Finsupp.single k 1) (a.erase k)) =
        a k * Λ' (Finsupp.single k 1) (a.erase k) by ring]
  simp only [Pi.smul_apply', Function.comp_apply, Units.smul_def, Subalgebra.smul_def,
    smul_eq_mul]

/-- The exchanged chart for `Λ'`, in which `y` replaces the `k`th coordinate of `M`. Its
monomials are `u ^ (-(a_k * Λ'(e_k, a°))) * y ^ a_k * M(a°)` with `a° = a - a_k e_k`.

The hypotheses ask that `Λ'` be alternating and agree with `Λ` on exponents vanishing at `k`,
that `y` quasi-commute with these monomials as the new `k`th coordinate of a chart for `Λ'`
would, and that the exchange element `y * M(e_k)` lie in their span. No hypothesis on `Λ`
itself is needed; it is alternating on the exponents vanishing at `k` because `Λ'` is. -/
noncomputable def exchange (M : BasedChart u Λ B) (k : I) (hΛ' : Λ'.IsAlt)
    (hΛΛ' : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 → Λ' a b = Λ a b) (y : Bˣ)
    (hy : ∀ a : I →₀ ℤ, a k = 0 → y * M.monomial a =
      Units.map (algebraMap R B) (u ^ (2 * Λ' (Finsupp.single k 1) a)) * (M.monomial a * y))
    (hyx : ((y * M.monomial (Finsupp.single k 1) : Bˣ) : B) ∈
      M.subalgebra (Finsupp.applyAddHom k).ker) :
    BasedChart u Λ' B where
  monomial := exchangeMonomial M k Λ' y
  monomial_zero := by simp [exchangeMonomial]
  monomial_mul := exchangeMonomial_mul M k hΛ' hΛΛ' hy
  linearIndependent := linearIndependent_exchangeMonomial M k hy hyx

/-- The exchanged chart built from cross terms: an additive map `l` on the exponents vanishing
at `k` and a unit `y` with `y * M(a) = u ^ (2 * l(a)) * M(a) * y` for these exponents and
`y * M(e_k)` in the span of their monomials. It is the chart for the exchanged form
`Λ.exchange k l`, which agrees with `Λ` off `k`, pairs `e_k` with `a°` by `l(a°)`, and is
alternating because `Λ` vanishes on the diagonal of the exponents vanishing at `k`. -/
noncomputable def exchangeOfDual (M : BasedChart u Λ B) (k : I)
    (hΛ : ∀ a : I →₀ ℤ, a k = 0 → Λ a a = 0)
    (l : Module.Dual ℤ (Finsupp.applyAddHom (M := ℤ) k).ker) (y : Bˣ)
    (hy : ∀ a : (Finsupp.applyAddHom (M := ℤ) k).ker, y * M.monomial a =
      Units.map (algebraMap R B) (u ^ (2 * l a)) * (M.monomial a * y))
    (hyx : ((y * M.monomial (Finsupp.single k 1) : Bˣ) : B) ∈
      M.subalgebra (Finsupp.applyAddHom k).ker) :
    BasedChart u (Λ.exchange k l) B :=
  M.exchange k (LinearMap.BilinForm.isAlt_exchange k hΛ l)
    (fun _ _ ha hb ↦ Λ.exchange_apply_of_apply_eq_zero l ha hb) y
    (fun a ha ↦ by
      have ha' : (⟨a.erase k, AddMonoidHom.mem_ker.mpr Finsupp.erase_same⟩ :
          (Finsupp.applyAddHom (M := ℤ) k).ker) = ⟨a, AddMonoidHom.mem_ker.mpr ha⟩ :=
        Subtype.ext (Finsupp.erase_of_notMem_support (Finsupp.notMem_support_iff.mpr ha))
      rw [LinearMap.BilinForm.exchange_single_self_apply, ha']
      exact hy ⟨a, _⟩)
    hyx

/-- The exchanged chart built from `l` is the exchanged chart for the form `Λ.exchange k l`,
so the general `exchange` API applies to it. -/
theorem exchangeOfDual_eq_exchange (M : BasedChart u Λ B) (k : I)
    (hΛ : ∀ a : I →₀ ℤ, a k = 0 → Λ a a = 0)
    (l : Module.Dual ℤ (Finsupp.applyAddHom (M := ℤ) k).ker) (y : Bˣ)
    (hy : ∀ a : (Finsupp.applyAddHom (M := ℤ) k).ker, y * M.monomial a =
      Units.map (algebraMap R B) (u ^ (2 * l a)) * (M.monomial a * y))
    (hyx : ((y * M.monomial (Finsupp.single k 1) : Bˣ) : B) ∈
      M.subalgebra (Finsupp.applyAddHom k).ker)
    (hΛ' : (Λ.exchange k l).IsAlt)
    (hΛΛ' : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 → Λ.exchange k l a b = Λ a b)
    (hy' : ∀ a : I →₀ ℤ, a k = 0 → y * M.monomial a =
      Units.map (algebraMap R B) (u ^ (2 * Λ.exchange k l (Finsupp.single k 1) a)) *
        (M.monomial a * y)) :
    M.exchangeOfDual k hΛ l y hy hyx = M.exchange k hΛ' hΛΛ' y hy' hyx :=
  (rfl)

/-- The monomials of the exchanged chart built from `l`: `u ^ (-(a_k * l(a°))) * y ^ a_k * M(a°)`.
-/
theorem exchangeOfDual_monomial (M : BasedChart u Λ B) (k : I)
    (hΛ : ∀ a : I →₀ ℤ, a k = 0 → Λ a a = 0)
    (l : Module.Dual ℤ (Finsupp.applyAddHom (M := ℤ) k).ker) (y : Bˣ)
    (hy : ∀ a : (Finsupp.applyAddHom (M := ℤ) k).ker, y * M.monomial a =
      Units.map (algebraMap R B) (u ^ (2 * l a)) * (M.monomial a * y))
    (hyx : ((y * M.monomial (Finsupp.single k 1) : Bˣ) : B) ∈
      M.subalgebra (Finsupp.applyAddHom k).ker) (a : I →₀ ℤ) :
    (M.exchangeOfDual k hΛ l y hy hyx).monomial a =
      Units.map (algebraMap R B)
          (u ^ (-(a k * l ⟨a.erase k, AddMonoidHom.mem_ker.mpr Finsupp.erase_same⟩))) *
        y ^ a k * M.monomial (a.erase k) := by
  simp [exchangeOfDual, exchange, exchangeMonomial]

variable (M : BasedChart u Λ B) (k : I) (hΛ' : Λ'.IsAlt)
  (hΛΛ' : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 → Λ' a b = Λ a b) (y : Bˣ)
  (hy : ∀ a : I →₀ ℤ, a k = 0 → y * M.monomial a =
    Units.map (algebraMap R B) (u ^ (2 * Λ' (Finsupp.single k 1) a)) * (M.monomial a * y))
  (hyx : ((y * M.monomial (Finsupp.single k 1) : Bˣ) : B) ∈
    M.subalgebra (Finsupp.applyAddHom k).ker)

/-- The monomials of the exchanged chart: `u ^ (-(a_k * Λ'(e_k, a°))) * y ^ a_k * M(a°)`. -/
theorem exchange_monomial (a : I →₀ ℤ) :
    (M.exchange k hΛ' hΛΛ' y hy hyx).monomial a =
      Units.map (algebraMap R B) (u ^ (-(a k * Λ' (Finsupp.single k 1) (a.erase k)))) *
        y ^ a k * M.monomial (a.erase k) :=
  (rfl)

/-- The exchanged chart keeps every monomial whose exponent vanishes at `k`. -/
@[simp]
theorem exchange_monomial_of_apply_eq_zero {a : I →₀ ℤ} (ha : a k = 0) :
    (M.exchange k hΛ' hΛΛ' y hy hyx).monomial a = M.monomial a := by
  rw [exchange_monomial, ha, Finsupp.erase_of_notMem_support (Finsupp.notMem_support_iff.mpr ha)]
  simp

/-- The `k`th coordinate of the exchanged chart is `y`. -/
@[simp]
theorem exchange_monomial_single_self :
    (M.exchange k hΛ' hΛΛ' y hy hyx).monomial (Finsupp.single k 1) = y := by
  simp [exchange_monomial]

/-- The coordinates of the exchanged chart away from `k` are those of `M`. -/
theorem exchange_monomial_single_of_ne {i : I} (hi : i ≠ k) :
    (M.exchange k hΛ' hΛΛ' y hy hyx).monomial (Finsupp.single i 1) =
      M.monomial (Finsupp.single i 1) :=
  M.exchange_monomial_of_apply_eq_zero k hΛ' hΛΛ' y hy hyx
    (Finsupp.single_eq_of_ne hi.symm)

/-- The exchanged chart has the same subalgebra as `M` on every set of exponents vanishing at
`k`, in particular on all of them. -/
theorem subalgebra_exchange {S : Type*} [SetLike S (I →₀ ℤ)] {N : S} (hN : ∀ a ∈ N, a k = 0) :
    (M.exchange k hΛ' hΛΛ' y hy hyx).subalgebra N = M.subalgebra N := by
  rw [subalgebra_eq_adjoin, subalgebra_eq_adjoin, Set.image_congr fun a ha ↦ by
    rw [M.exchange_monomial_of_apply_eq_zero k hΛ' hΛΛ' y hy hyx (hN a ha)]]

/-- The exchanged chart built from `l` has the same subalgebra as `M` on every set of exponents
vanishing at `k`. -/
theorem subalgebra_exchangeOfDual (hΛ : ∀ a : I →₀ ℤ, a k = 0 → Λ a a = 0)
    (l : Module.Dual ℤ (Finsupp.applyAddHom (M := ℤ) k).ker)
    (hl : ∀ a : (Finsupp.applyAddHom (M := ℤ) k).ker, y * M.monomial a =
      Units.map (algebraMap R B) (u ^ (2 * l a)) * (M.monomial a * y))
    {S : Type*} [SetLike S (I →₀ ℤ)] {N : S} (hN : ∀ a ∈ N, a k = 0) :
    (M.exchangeOfDual k hΛ l y hl hyx).subalgebra N = M.subalgebra N :=
  M.subalgebra_exchange k _ _ y _ hyx hN

/-- The exchanged chart built from `l` keeps every monomial whose exponent vanishes at `k`. -/
@[simp]
theorem exchangeOfDual_monomial_of_apply_eq_zero (hΛ : ∀ a : I →₀ ℤ, a k = 0 → Λ a a = 0)
    (l : Module.Dual ℤ (Finsupp.applyAddHom (M := ℤ) k).ker)
    (hl : ∀ a : (Finsupp.applyAddHom (M := ℤ) k).ker, y * M.monomial a =
      Units.map (algebraMap R B) (u ^ (2 * l a)) * (M.monomial a * y))
    {a : I →₀ ℤ} (ha : a k = 0) :
    (M.exchangeOfDual k hΛ l y hl hyx).monomial a = M.monomial a :=
  M.exchange_monomial_of_apply_eq_zero k _ _ y _ hyx ha

/-- The `k`th coordinate of the exchanged chart built from `l` is `y`. -/
@[simp]
theorem exchangeOfDual_monomial_single_self (hΛ : ∀ a : I →₀ ℤ, a k = 0 → Λ a a = 0)
    (l : Module.Dual ℤ (Finsupp.applyAddHom (M := ℤ) k).ker)
    (hl : ∀ a : (Finsupp.applyAddHom (M := ℤ) k).ker, y * M.monomial a =
      Units.map (algebraMap R B) (u ^ (2 * l a)) * (M.monomial a * y)) :
    (M.exchangeOfDual k hΛ l y hl hyx).monomial (Finsupp.single k 1) = y :=
  M.exchange_monomial_single_self k _ _ y _ hyx

/-- The coordinates of the exchanged chart built from `l` away from `k` are those of `M`. -/
theorem exchangeOfDual_monomial_single_of_ne (hΛ : ∀ a : I →₀ ℤ, a k = 0 → Λ a a = 0)
    (l : Module.Dual ℤ (Finsupp.applyAddHom (M := ℤ) k).ker)
    (hl : ∀ a : (Finsupp.applyAddHom (M := ℤ) k).ker, y * M.monomial a =
      Units.map (algebraMap R B) (u ^ (2 * l a)) * (M.monomial a * y))
    {i : I} (hi : i ≠ k) :
    (M.exchangeOfDual k hΛ l y hl hyx).monomial (Finsupp.single i 1) =
      M.monomial (Finsupp.single i 1) :=
  M.exchange_monomial_single_of_ne k _ _ y _ hyx hi

/-- The exchanged chart is the only chart for `Λ'` whose `k`th coordinate is `y` and whose
other coordinates are those of `M`. -/
theorem eq_exchange {M' : BasedChart u Λ' B} (hk : M'.monomial (Finsupp.single k 1) = y)
    (hi : ∀ i, i ≠ k → M'.monomial (Finsupp.single i 1) = M.monomial (Finsupp.single i 1)) :
    M' = M.exchange k hΛ' hΛΛ' y hy hyx := by
  refine ext_coordinate Finsupp.basisSingleOne fun i ↦ ?_
  simp only [coordinate_def, Finsupp.coe_basisSingleOne]
  obtain rfl | hik := eq_or_ne i k
  · rw [hk, exchange_monomial_single_self]
  · rw [hi i hik, M.exchange_monomial_single_of_ne k hΛ' hΛΛ' y hy hyx hik]

/-- The exchanged chart built from `l` is the only chart for `Λ.exchange k l` whose `k`th
coordinate is `y` and whose other coordinates are those of `M`. -/
theorem eq_exchangeOfDual (hΛ : ∀ a : I →₀ ℤ, a k = 0 → Λ a a = 0)
    (l : Module.Dual ℤ (Finsupp.applyAddHom (M := ℤ) k).ker)
    (hl : ∀ a : (Finsupp.applyAddHom (M := ℤ) k).ker, y * M.monomial a =
      Units.map (algebraMap R B) (u ^ (2 * l a)) * (M.monomial a * y))
    {M' : BasedChart u (Λ.exchange k l) B} (hk : M'.monomial (Finsupp.single k 1) = y)
    (hi : ∀ i, i ≠ k → M'.monomial (Finsupp.single i 1) = M.monomial (Finsupp.single i 1)) :
    M' = M.exchangeOfDual k hΛ l y hl hyx :=
  M.eq_exchange k _ _ y _ hyx hk hi

end Exchange

end BasedChart

end TauCeti
