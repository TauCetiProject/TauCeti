/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.BasedChart.Basic
public import TauCeti.Algebra.Cluster.OneExchange.Independence
public import TauCeti.RingTheory.AlgebraTower

/-!
# One exchange of a based chart

Let `M` be a based chart for `(R, u, Λ)` in an `R`-algebra `B`, with exponents `I →₀ ℤ`, and
fix a direction `k`. The monomials whose exponent vanishes at `k` span a subalgebra `C`, and
the coordinate `x = M(e_k)` has unique left coefficients in `C` for its integer powers. A unit
`y` with `y * x ∈ C`, quasi-commuting with every monomial of `C` according to an alternating
form `Λ'` that agrees with `Λ` off `k`, then defines a new based chart for `(R, u, Λ')`:

`M'(a) = u ^ (-(a_k * Λ'(e_k, a°))) * y ^ a_k * M(a°)`, where `a° = a - a_k e_k`.

Its coordinate in direction `k` is `y` and its other coordinates are those of `M`. The
exchange element `E = y * x` normalizes `C`, so `y = E * x⁻¹` is a skew exchange in the sense
of `TauCeti.linearIndependent_mul_inv_zpow`. Neither the multiplication rule nor faithfulness
of the new chart is assumed, and the ambient algebra need not be a division ring; this is the
chart a seed mutation produces from an invertible exchange element.

The general material is stated for any exponent group `L`: `BasedChart.subalgebra M N`
is the span of the monomials with exponents in a subgroup `N`, conjugation by a unit that
maps these monomials into it maps all of it into itself, and the powers of a monomial
transverse to `N` have unique left coefficients in it
(`BasedChart.linearIndependent_zpow_monomial`).

For the data of §0.5, an additive map `l` on the exponents vanishing at `k` in place of `Λ'`,
`LinearMap.BilinForm.exchange Λ k l` is the alternating form
`Λ'(a, b) = Λ(a°, b°) + a_k * l(b°) - b_k * l(a°)`, and `BasedChart.exchangeOfDual` is the
exchanged chart for it.

## Main definitions

* `TauCeti.BasedChart.subalgebra`: the span of the chart monomials with exponents in `N`.
* `TauCeti.BasedChart.exchange`: the based chart obtained by exchanging the `k`th coordinate.
* `LinearMap.BilinForm.exchange`: the alternating form of the exchanged chart, built from `Λ`
  and the cross terms `l`.
* `TauCeti.BasedChart.exchangeOfDual`: the exchanged chart for this form.

## Main results

* `TauCeti.BasedChart.linearIndependent_zpow_monomial`: unique left coefficients for powers of
  a monomial transverse to `N`.
* `TauCeti.BasedChart.mul_single_mul_mul_inv_mem_subalgebra_iff`: the exchange element
  `y * x` normalizes the other-coordinate subalgebra.
* `TauCeti.BasedChart.eq_exchange`: the exchanged chart is the only chart for `Λ'` with these
  coordinates.

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

/-- The form of the chart exchanged in direction `k` with cross terms `l` (§0.5), an additive map
on the exponents vanishing at `k`: it agrees with `Λ` on these exponents and pairs `e_k` with
them by `l`, namely `Λ'(a, b) = Λ(a°, b°) + a_k * l(b°) - b_k * l(a°)` with
`a° = a - a_k e_k`. -/
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
        b k * l ⟨a.erase k, AddMonoidHom.mem_ker.mpr Finsupp.erase_same⟩ :=
  (rfl)

/-- The exchanged form of an alternating form is alternating. -/
theorem isAlt_exchange {Λ : LinearMap.BilinForm ℤ (I →₀ ℤ)} (hΛ : Λ.IsAlt) (k : I)
    (l : Module.Dual ℤ (Finsupp.applyAddHom (M := ℤ) k).ker) : (Λ.exchange k l).IsAlt :=
  fun a ↦ by rw [exchange_apply, hΛ.self_eq_zero, zero_add, sub_self]

/-- The exchanged form agrees with `Λ` on exponents vanishing at `k`. -/
theorem exchange_apply_of_apply_eq_zero (Λ : LinearMap.BilinForm ℤ (I →₀ ℤ)) {k : I}
    (l : Module.Dual ℤ (Finsupp.applyAddHom (M := ℤ) k).ker) {a b : I →₀ ℤ} (ha : a k = 0)
    (hb : b k = 0) : Λ.exchange k l a b = Λ a b := by
  rw [exchange_apply, ha, hb, zero_mul, zero_mul, add_zero, sub_zero,
    Finsupp.erase_of_notMem_support (by simpa using ha),
    Finsupp.erase_of_notMem_support (by simpa using hb)]

/-- The exchanged form pairs `e_k` with `b` by `l(b°)`. -/
@[simp]
theorem exchange_single_self_apply (Λ : LinearMap.BilinForm ℤ (I →₀ ℤ)) (k : I)
    (l : Module.Dual ℤ (Finsupp.applyAddHom (M := ℤ) k).ker) (b : I →₀ ℤ) :
    Λ.exchange k l (Finsupp.single k 1) b =
      l ⟨b.erase k, AddMonoidHom.mem_ker.mpr Finsupp.erase_same⟩ := by
  simp only [exchange_apply, Finsupp.erase_single, Finsupp.single_eq_same, one_mul, map_zero]
  rw [LinearMap.zero_apply, zero_add, sub_eq_self, mul_eq_zero]
  exact Or.inr (map_zero l)

end LinearMap.BilinForm

namespace TauCeti

namespace BasedChart

section Subalgebra

variable {R L B : Type*} [CommSemiring R] [AddCommGroup L] [Semiring B] [Algebra R B]
  {u : Rˣ} {Λ : LinearMap.BilinForm ℤ L}

/-- The products of two monomials with exponents in `N` are scalar multiples of a monomial with
exponent in `N`, so their span is closed under multiplication. -/
private theorem mul_mem_span_monomial (M : BasedChart u Λ B) (N : AddSubgroup L) {c d : B}
    (hc : c ∈ Submodule.span R ((fun a ↦ (M.monomial a : B)) '' N))
    (hd : d ∈ Submodule.span R ((fun a ↦ (M.monomial a : B)) '' N)) :
    c * d ∈ Submodule.span R ((fun a ↦ (M.monomial a : B)) '' N) := by
  have h := Submodule.mul_mem_mul hc hd
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_le.mpr ?_ h
  rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
  dsimp only
  rw [SetLike.mem_coe, val_monomial_mul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a + b, N.add_mem ha hb, rfl⟩)

/-- The subalgebra spanned over `R` by the chart monomials with exponents in a subgroup `N`.
It is the image of the based quantum torus on `N` under the chart. -/
noncomputable def subalgebra (M : BasedChart u Λ B) (N : AddSubgroup L) : Subalgebra R B :=
  (Submodule.span R ((fun a ↦ (M.monomial a : B)) '' N)).toSubalgebra
    (Submodule.subset_span ⟨0, N.zero_mem, by simp⟩)
    (fun _ _ ↦ mul_mem_span_monomial M N)

/-- Membership in the subalgebra of `N` is membership in the `R`-span of its monomials. -/
theorem mem_subalgebra_iff (M : BasedChart u Λ B) (N : AddSubgroup L) {c : B} :
    c ∈ M.subalgebra N ↔ c ∈ Submodule.span R ((fun a ↦ (M.monomial a : B)) '' N) :=
  Iff.rfl

/-- The underlying submodule of the subalgebra of `N` is the span of its monomials. -/
@[simp]
theorem toSubmodule_subalgebra (M : BasedChart u Λ B) (N : AddSubgroup L) :
    Subalgebra.toSubmodule (M.subalgebra N) =
      Submodule.span R ((fun a ↦ (M.monomial a : B)) '' N) :=
  Submodule.toSubalgebra_toSubmodule ..

/-- Every monomial with exponent in `N` lies in the subalgebra of `N`. -/
theorem monomial_mem_subalgebra (M : BasedChart u Λ B) {N : AddSubgroup L} {a : L}
    (ha : a ∈ N) : (M.monomial a : B) ∈ M.subalgebra N :=
  Submodule.subset_span ⟨a, ha, rfl⟩

/-- The subalgebra of `N` is the smallest subalgebra containing the monomials of `N`. -/
theorem subalgebra_le_iff (M : BasedChart u Λ B) {N : AddSubgroup L} {S : Subalgebra R B} :
    M.subalgebra N ≤ S ↔ ∀ a ∈ N, (M.monomial a : B) ∈ S := by
  refine ⟨fun h a ha ↦ h (M.monomial_mem_subalgebra ha), fun h c hc ↦ ?_⟩
  refine (Submodule.span_le (p := Subalgebra.toSubmodule S)).mpr ?_
    ((M.mem_subalgebra_iff N).mp hc)
  rintro _ ⟨a, ha, rfl⟩
  exact h a ha

/-- The subalgebra of `N` is the subalgebra generated by the monomials of `N`. -/
theorem subalgebra_eq_adjoin (M : BasedChart u Λ B) (N : AddSubgroup L) :
    M.subalgebra N = Algebra.adjoin R ((fun a ↦ (M.monomial a : B)) '' N) :=
  le_antisymm (M.subalgebra_le_iff.mpr fun a ha ↦ Algebra.subset_adjoin ⟨a, ha, rfl⟩)
    (Algebra.adjoin_le <| by
      rintro _ ⟨a, ha, rfl⟩
      exact M.monomial_mem_subalgebra ha)

/-- The monomials of `N`, viewed in the subalgebra of `N`, span it over `R`. -/
theorem span_range_monomial_subalgebra (M : BasedChart u Λ B) (N : AddSubgroup L) :
    Submodule.span R (Set.range fun a : N ↦
      (⟨M.monomial a, M.monomial_mem_subalgebra a.property⟩ : M.subalgebra N)) = ⊤ := by
  refine eq_top_iff.mpr fun c _ ↦ ?_
  have hc : (c : B) ∈ Submodule.map (M.subalgebra N).val.toLinearMap
      (Submodule.span R (Set.range fun a : N ↦
        (⟨M.monomial a, M.monomial_mem_subalgebra a.property⟩ : M.subalgebra N))) := by
    have hrange : Set.range ((M.subalgebra N).val.toLinearMap ∘ fun a : N ↦
        (⟨M.monomial a, M.monomial_mem_subalgebra a.property⟩ : M.subalgebra N)) =
          (fun a ↦ (M.monomial a : B)) '' N := by
      ext
      simp
    rw [Submodule.map_span, ← Set.range_comp, hrange, ← mem_subalgebra_iff]
    exact c.property
  obtain ⟨d, hd, hdc⟩ := hc
  rwa [show d = c from Subtype.ext hdc] at hd

/-- If conjugation by a unit maps every monomial of `N` into the subalgebra of `N`, it maps the
whole subalgebra into itself. -/
theorem mul_mul_inv_mem_subalgebra (M : BasedChart u Λ B) {N : AddSubgroup L} {g : Bˣ}
    (hg : ∀ a ∈ N, (g : B) * M.monomial a * ↑g⁻¹ ∈ M.subalgebra N) {c : B}
    (hc : c ∈ M.subalgebra N) : (g : B) * c * ↑g⁻¹ ∈ M.subalgebra N := by
  rw [mem_subalgebra_iff] at hc
  induction hc using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨a, ha, rfl⟩ := h
    exact hg a ha
  | zero => simp
  | add c d _ _ hc hd => simpa [mul_add, add_mul] using add_mem hc hd
  | smul r c _ hc => simpa [mul_smul_comm, smul_mul_assoc] using Subalgebra.smul_mem _ hc r

/-- For an alternating form, conjugation by any chart monomial maps the subalgebra of `N` into
itself, since it rescales each monomial by a power of `u`. -/
theorem monomial_mul_mul_inv_mem_subalgebra (M : BasedChart u Λ B) (hΛ : Λ.IsAlt)
    {N : AddSubgroup L} (b : L) {c : B} (hc : c ∈ M.subalgebra N) :
    (M.monomial b : B) * c * ↑(M.monomial b)⁻¹ ∈ M.subalgebra N := by
  refine M.mul_mul_inv_mem_subalgebra (fun a ha ↦ ?_) hc
  rw [M.val_monomial_mul_monomial_eq_smul_mul hΛ, smul_mul_assoc, mul_assoc,
    Units.mul_inv, mul_one]
  exact Subalgebra.smul_mem _ (M.monomial_mem_subalgebra ha) _

/-- For an alternating form, conjugation by the inverse of any chart monomial maps the
subalgebra of `N` into itself. -/
theorem monomial_inv_mul_mul_mem_subalgebra (M : BasedChart u Λ B) (hΛ : Λ.IsAlt)
    {N : AddSubgroup L} (b : L) {c : B} (hc : c ∈ M.subalgebra N) :
    (↑(M.monomial b)⁻¹ : B) * c * M.monomial b ∈ M.subalgebra N := by
  simpa [M.monomial_inv hΛ] using M.monomial_mul_mul_inv_mem_subalgebra hΛ (-b) hc

/-- If no nonzero multiple of `e` lies in `N`, the integer powers of the monomial at `e` have
unique left coefficients in the subalgebra of `N`. -/
theorem linearIndependent_zpow_monomial (M : BasedChart u Λ B) (hΛ : Λ.IsAlt)
    {N : AddSubgroup L} {e : L} (he : ∀ n : ℤ, n • e ∈ N → n = 0) :
    LinearIndependent (M.subalgebra N) fun n : ℤ ↦ ((M.monomial e ^ n : Bˣ) : B) := by
  refine LinearIndependent.of_smul_of_span_eq_top ?_ (M.span_range_monomial_subalgebra N)
  have hinj : Function.Injective fun p : N × ℤ ↦ (p.1 : L) + p.2 • e := by
    rintro ⟨a, n⟩ ⟨b, m⟩ h
    have hnm : n = m := by
      have h' : (n - m) • e = (b : L) - a := by
        simp only at h
        calc (n - m) • e = ((a : L) + n • e) - a - m • e := by rw [sub_smul]; abel
          _ = b - a := by rw [h]; abel
      exact sub_eq_zero.mp (he _ (h' ▸ N.sub_mem b.property a.property))
    subst hnm
    exact Prod.ext (Subtype.ext (add_right_cancel h)) rfl
  convert (M.linearIndependent.comp _ hinj).units_smul
    (fun p : N × ℤ ↦ u ^ (Λ p.1 (p.2 • e))) using 1
  funext p
  rw [Subalgebra.smul_def, M.monomial_zpow hΛ, smul_eq_mul, val_monomial_mul]
  simp only [Pi.smul_apply', Function.comp_apply, Units.smul_def]

end Subalgebra

section Exchange

variable {R I B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]
  {u : Rˣ} {Λ Λ' : LinearMap.BilinForm ℤ (I →₀ ℤ)}

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
  have hcomm := val_zpow_mul_monomial M k hy (a := a.erase k) Finsupp.erase_same (b k)
  have hswap : (M.monomial (a.erase k) : B) * ↑(y ^ b k) =
      ((u ^ (-(b k * (2 * Λ' (Finsupp.single k 1) (a.erase k)))) : Rˣ) : R) •
        (((y ^ b k : Bˣ) : B) * M.monomial (a.erase k)) := by
    rw [hcomm, smul_smul, ← Units.val_mul (α := R), ← zpow_add, neg_add_cancel, zpow_zero,
      Units.val_one, one_smul]
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
  rw [Units.val_mul, Units.val_mul, val_exchangeMonomial, val_exchangeMonomial,
    val_exchangeMonomial, smul_mul_smul_comm, hprod, Units.coe_map, MonoidHom.coe_ofClass,
    ← Algebra.smul_def]
  simp only [smul_smul]
  congr 1
  simp only [← Units.val_mul (α := R), ← zpow_add]
  congr 2
  -- Expand `Λ' a b` along `a = a_k e_k + a°` and `b = b_k e_k + b°`.
  have hs (n : ℤ) : Finsupp.single k n = n • Finsupp.single k (1 : ℤ) := by
    rw [Finsupp.smul_single_one]
  have hab : Λ' a b = a k * Λ' (Finsupp.single k 1) (b.erase k) -
      b k * Λ' (Finsupp.single k 1) (a.erase k) + Λ' (a.erase k) (b.erase k) := by
    conv_lhs => rw [← Finsupp.single_add_erase k a, ← Finsupp.single_add_erase k b,
      hs (a k), hs (b k)]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hΛ'.self_eq_zero, ← hΛ'.neg_eq (a.erase k)]
    ring
  rw [hab, hΛΛ' _ _ Finsupp.erase_same Finsupp.erase_same, Finsupp.erase_add,
    Finsupp.add_apply, map_add]
  ring

/-- The exchanged monomials are linearly independent over `R`. -/
private theorem linearIndependent_exchangeMonomial (M : BasedChart u Λ B) (hΛ : Λ.IsAlt)
    (k : I) {y : Bˣ}
    (hy : ∀ a : I →₀ ℤ, a k = 0 → y * M.monomial a =
      Units.map (algebraMap R B) (u ^ (2 * Λ' (Finsupp.single k 1) a)) * (M.monomial a * y))
    (hyx : ((y * M.monomial (Finsupp.single k 1) : Bˣ) : B) ∈
      M.subalgebra (Finsupp.applyAddHom k).ker) :
    LinearIndependent R fun a ↦ (exchangeMonomial M k Λ' y a : B) := by
  set N : AddSubgroup (I →₀ ℤ) := (Finsupp.applyAddHom k).ker with hN_def
  have hN {a : I →₀ ℤ} : a ∈ N ↔ a k = 0 := by simp [hN_def]
  -- Powers of the old coordinate, then of `y`, have unique left coefficients in `C`.
  have hx := M.linearIndependent_zpow_monomial hΛ (N := N)
    (e := Finsupp.single k 1) fun n hn ↦ by simpa using hN.mp hn
  have hyC := linearIndependent_mul_inv_zpow _ _ _
    (fun _ ↦ M.monomial_inv_mul_mul_mem_subalgebra hΛ (Finsupp.single k 1)) hyx hx
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
  rw [val_exchangeMonomial, val_zpow_mul_monomial M k hy Finsupp.erase_same, smul_smul,
    ← Units.val_mul, ← zpow_add]
  simp only [Pi.smul_apply', Function.comp_apply, Units.smul_def, Subalgebra.smul_def,
    smul_eq_mul]
  congr 3
  ring

/-- The exchange element `E = y * M(e_k)` normalizes the span of the monomials whose
exponent vanishes at `k`: conjugation by `E` maps this subalgebra onto itself. -/
theorem mul_single_mul_mul_inv_mem_subalgebra_iff (M : BasedChart u Λ B) (hΛ : Λ.IsAlt)
    (k : I) {y : Bˣ}
    (hy : ∀ a : I →₀ ℤ, a k = 0 → y * M.monomial a =
      Units.map (algebraMap R B) (u ^ (2 * Λ' (Finsupp.single k 1) a)) * (M.monomial a * y))
    {c : B} :
    ((y * M.monomial (Finsupp.single k 1) : Bˣ) : B) * c *
        ↑(y * M.monomial (Finsupp.single k 1))⁻¹ ∈ M.subalgebra (Finsupp.applyAddHom k).ker ↔
      c ∈ M.subalgebra (Finsupp.applyAddHom k).ker := by
  have hyn (n : ℤ) {d : B} (hd : d ∈ M.subalgebra (Finsupp.applyAddHom k).ker) :
      ((y ^ n : Bˣ) : B) * d * ↑(y ^ n)⁻¹ ∈ M.subalgebra (Finsupp.applyAddHom k).ker := by
    refine M.mul_mul_inv_mem_subalgebra (fun a ha ↦ ?_) hd
    rw [val_zpow_mul_monomial M k hy (by simpa using ha), smul_mul_assoc, mul_assoc,
      Units.mul_inv, mul_one]
    exact Subalgebra.smul_mem _ (M.monomial_mem_subalgebra ha) _
  constructor
  · intro hc
    simpa [mul_assoc] using
      M.monomial_inv_mul_mul_mem_subalgebra hΛ (Finsupp.single k 1) (hyn (-1) hc)
  · intro hc
    simpa [mul_assoc] using
      hyn 1 (M.monomial_mul_mul_inv_mem_subalgebra hΛ (Finsupp.single k 1) hc)

/-- The exchanged chart for `Λ'`, in which `y` replaces the `k`th coordinate of `M`. Its
monomials are `u ^ (-(a_k * Λ'(e_k, a°))) * y ^ a_k * M(a°)` with `a° = a - a_k e_k`.

The hypotheses ask that `Λ'` be alternating and agree with `Λ` on exponents vanishing at `k`,
that `y` quasi-commute with these monomials as the new `k`th coordinate of a chart for `Λ'`
would, and that the exchange element `y * M(e_k)` lie in their span. -/
noncomputable def exchange (M : BasedChart u Λ B) (hΛ : Λ.IsAlt) (k : I) (hΛ' : Λ'.IsAlt)
    (hΛΛ' : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 → Λ' a b = Λ a b) (y : Bˣ)
    (hy : ∀ a : I →₀ ℤ, a k = 0 → y * M.monomial a =
      Units.map (algebraMap R B) (u ^ (2 * Λ' (Finsupp.single k 1) a)) * (M.monomial a * y))
    (hyx : ((y * M.monomial (Finsupp.single k 1) : Bˣ) : B) ∈
      M.subalgebra (Finsupp.applyAddHom k).ker) :
    BasedChart u Λ' B where
  monomial := exchangeMonomial M k Λ' y
  monomial_zero := by simp [exchangeMonomial]
  monomial_mul := exchangeMonomial_mul M k hΛ' hΛΛ' hy
  linearIndependent := linearIndependent_exchangeMonomial M hΛ k hy hyx

/-- The exchanged chart built from the data of §0.5: an additive map `l` on the exponents
vanishing at `k` and a unit `y` with `y * M(a) = u ^ (2 * l(a)) * M(a) * y` for these exponents
and `y * M(e_k)` in the span of their monomials. It is the chart for the alternating form
`Λ.exchange k l`, which agrees with `Λ` off `k` and pairs `e_k` with `a°` by `l(a°)`. -/
noncomputable def exchangeOfDual (M : BasedChart u Λ B) (hΛ : Λ.IsAlt) (k : I)
    (l : Module.Dual ℤ (Finsupp.applyAddHom (M := ℤ) k).ker) (y : Bˣ)
    (hy : ∀ a : (Finsupp.applyAddHom (M := ℤ) k).ker, y * M.monomial a =
      Units.map (algebraMap R B) (u ^ (2 * l a)) * (M.monomial a * y))
    (hyx : ((y * M.monomial (Finsupp.single k 1) : Bˣ) : B) ∈
      M.subalgebra (Finsupp.applyAddHom k).ker) :
    BasedChart u (Λ.exchange k l) B :=
  M.exchange hΛ k (LinearMap.BilinForm.isAlt_exchange hΛ k l)
    (fun _ _ ha hb ↦ Λ.exchange_apply_of_apply_eq_zero l ha hb) y
    (fun a ha ↦ by
      simpa [Finsupp.erase_of_notMem_support (show k ∉ a.support by simpa using ha)] using
        hy ⟨a, AddMonoidHom.mem_ker.mpr ha⟩)
    hyx

/-- The monomials of the exchanged chart built from `l`: `u ^ (-(a_k * l(a°))) * y ^ a_k * M(a°)`.
-/
theorem exchangeOfDual_monomial (M : BasedChart u Λ B) (hΛ : Λ.IsAlt) (k : I)
    (l : Module.Dual ℤ (Finsupp.applyAddHom (M := ℤ) k).ker) (y : Bˣ)
    (hy : ∀ a : (Finsupp.applyAddHom (M := ℤ) k).ker, y * M.monomial a =
      Units.map (algebraMap R B) (u ^ (2 * l a)) * (M.monomial a * y))
    (hyx : ((y * M.monomial (Finsupp.single k 1) : Bˣ) : B) ∈
      M.subalgebra (Finsupp.applyAddHom k).ker) (a : I →₀ ℤ) :
    (M.exchangeOfDual hΛ k l y hy hyx).monomial a =
      Units.map (algebraMap R B)
          (u ^ (-(a k * l ⟨a.erase k, AddMonoidHom.mem_ker.mpr Finsupp.erase_same⟩))) *
        y ^ a k * M.monomial (a.erase k) := by
  simp [exchangeOfDual, exchange, exchangeMonomial]

variable (M : BasedChart u Λ B) (hΛ : Λ.IsAlt) (k : I) (hΛ' : Λ'.IsAlt)
  (hΛΛ' : ∀ a b : I →₀ ℤ, a k = 0 → b k = 0 → Λ' a b = Λ a b) (y : Bˣ)
  (hy : ∀ a : I →₀ ℤ, a k = 0 → y * M.monomial a =
    Units.map (algebraMap R B) (u ^ (2 * Λ' (Finsupp.single k 1) a)) * (M.monomial a * y))
  (hyx : ((y * M.monomial (Finsupp.single k 1) : Bˣ) : B) ∈
    M.subalgebra (Finsupp.applyAddHom k).ker)

/-- The monomials of the exchanged chart: `u ^ (-(a_k * Λ'(e_k, a°))) * y ^ a_k * M(a°)`. -/
theorem exchange_monomial (a : I →₀ ℤ) :
    (M.exchange hΛ k hΛ' hΛΛ' y hy hyx).monomial a =
      Units.map (algebraMap R B) (u ^ (-(a k * Λ' (Finsupp.single k 1) (a.erase k)))) *
        y ^ a k * M.monomial (a.erase k) :=
  (rfl)

/-- The exchanged chart keeps every monomial whose exponent vanishes at `k`. -/
@[simp]
theorem exchange_monomial_of_apply_eq_zero {a : I →₀ ℤ} (ha : a k = 0) :
    (M.exchange hΛ k hΛ' hΛΛ' y hy hyx).monomial a = M.monomial a := by
  rw [exchange_monomial, ha, Finsupp.erase_of_notMem_support (by simpa using ha)]
  simp

/-- The `k`th coordinate of the exchanged chart is `y`. -/
@[simp]
theorem exchange_monomial_single_self :
    (M.exchange hΛ k hΛ' hΛΛ' y hy hyx).monomial (Finsupp.single k 1) = y := by
  simp [exchange_monomial]

/-- The coordinates of the exchanged chart away from `k` are those of `M`. -/
theorem exchange_monomial_single_of_ne {i : I} (hi : i ≠ k) :
    (M.exchange hΛ k hΛ' hΛΛ' y hy hyx).monomial (Finsupp.single i 1) =
      M.monomial (Finsupp.single i 1) :=
  M.exchange_monomial_of_apply_eq_zero hΛ k hΛ' hΛΛ' y hy hyx
    (Finsupp.single_eq_of_ne hi.symm)

/-- The exchanged chart is the only chart for `Λ'` whose `k`th coordinate is `y` and whose
other coordinates are those of `M`. -/
theorem eq_exchange {M' : BasedChart u Λ' B} (hk : M'.monomial (Finsupp.single k 1) = y)
    (hi : ∀ i, i ≠ k → M'.monomial (Finsupp.single i 1) = M.monomial (Finsupp.single i 1)) :
    M' = M.exchange hΛ k hΛ' hΛΛ' y hy hyx := by
  refine ext_coordinate Finsupp.basisSingleOne fun i ↦ ?_
  simp only [coordinate_def, Finsupp.coe_basisSingleOne]
  obtain rfl | hik := eq_or_ne i k
  · rw [hk, exchange_monomial_single_self]
  · rw [hi i hik, M.exchange_monomial_single_of_ne hΛ k hΛ' hΛΛ' y hy hyx hik]

end Exchange

end BasedChart

end TauCeti
