/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Basic
public import TauCeti.Algebra.BigOperators.Finprod

/-!
# Linear maps of completed combinations given by supported kernels

Let `F₁ : S₁ → ℝ` and `F₀ : S₀ → ℝ` be potentials, and let `m : S₁ → S₀ → R` be a *kernel*:
`m p₁ p₀` is the coefficient of the output generator `p₀` in the image of the input generator
`p₁`. Suppose that

* `m p₁ p₀ ≠ 0` implies `F₀ p₀ ≤ F₁ p₁ + C` for a fixed constant `C`, and
* each output function `m p₁` is itself a completed combination.

Then for a completed combination `a` the sum `∑ a(p₁) m(p₁, p₀)` has finitely many nonzero terms,
and it defines a linear map `NovikovModule R F₁ → NovikovModule R F₀`
(`NovikovModule.kernelMap`), which shifts potential cutoffs by `C`.

Floer and Novikov differentials, continuation maps, chain homotopies and comparison maps are all
of this form: the generators are lifted critical points or capped orbits, the potentials are the
action functionals, `m` counts rigid trajectories, and the potential bound is the energy estimate.
The kernel of a composite is the matrix product `∑ m(p₁, p₀) m'(p₀, p₂)` of the two kernels
(`NovikovModule.kernelComp`). It is again supported, with the sum of the two constants, and the
composite of the two linear maps is the linear map of the composite kernel
(`NovikovModule.kernelMap_kernelMap`). Hence identities between chain maps, such as `d ∘ d = 0`
or `f ∘ g - id = d ∘ h + h ∘ d`, follow from the corresponding identities between kernels.

Suppose next that each `Sₗ` is a finite disjoint union of torsors under a group `H` with
equivariant potentials, and that the kernel is unchanged when the input and the output are
translated by the same element. In lift coordinates the map is given by the matrix of Novikov
series of the kernel in the reference generators (`NovikovModule.coordinates_kernelMap`), so it is
linear over the Novikov ring (`NovikovModule.novikovKernelMap`). No discreteness or injectivity of
the periods is assumed.

## Main definitions

* `TauCeti.NovikovModule.kernelMap`: the linear map given by a supported kernel.
* `TauCeti.NovikovModule.kernelComp`: the composite of two kernels.
* `TauCeti.NovikovModule.novikovKernelMap`: the map of an invariant kernel, as a linear map over
  the Novikov ring.

## Main results

* `TauCeti.NovikovModule.kernelMap_apply_val_eq_zero`: the map shifts potential cutoffs by the
  constant of the potential bound.
* `TauCeti.NovikovModule.potential_le_of_kernelComp_ne_zero`,
  `TauCeti.NovikovModule.kernelComp_mem`: the composite kernel is supported.
* `TauCeti.NovikovModule.kernelMap_kernelMap`: composition of maps is composition of kernels.
* `TauCeti.NovikovModule.kernelMap_add`, `TauCeti.NovikovModule.kernelMap_zero`: the map is
  additive in the kernel.
* `TauCeti.NovikovModule.kernelMap_eq_id`: the identity kernel gives the identity map.
* `TauCeti.NovikovModule.coordinates_kernelMap`: the matrix formula in lift coordinates.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 3.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*,
  IAS/Park City Math. Ser. 7 (1999), 143–229.
-/

public section

noncomputable section

open Function

namespace TauCeti

namespace NovikovModule

section Map

variable {R S₁ S₂ S₀ : Type*} [Semiring R] {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ}

/-- Under a potential bound, only finitely many terms of a sum of kernel values weighted by a
completed combination are nonzero. -/
theorem finite_support_mul {S : Type*} {F : S → ℝ} {κ : S → R} {T : ℝ}
    (hκ : ∀ s, κ s ≠ 0 → T ≤ F s) (c : NovikovModule R F) :
    (support fun s => c.val s * κ s).Finite :=
  (finite_ge c T).subset fun s hs => ⟨left_ne_zero_of_mul hs, hκ s (right_ne_zero_of_mul hs)⟩

/-- Summing completed outputs of a kernel with a potential bound against a completed combination
gives a completed combination. -/
theorem finsum_mul_mem {S : Type*} {F : S → ℝ} {κ : S → S₀ → R} {D : ℝ}
    (hκ : ∀ s p₀, κ s p₀ ≠ 0 → F₀ p₀ ≤ F s + D) (hκfin : ∀ s, κ s ∈ NovikovModule R F₀)
    (c : NovikovModule R F) :
    (fun p₀ => ∑ᶠ s, c.val s * κ s p₀) ∈ NovikovModule R F₀ := by
  refine mem_iff.2 fun T => ((finite_ge c (T - D)).biUnion
    fun s _ => mem_iff.1 (hκfin s) T).subset ?_
  rintro p₀ ⟨hp, hT⟩
  obtain ⟨s, hs⟩ : ∃ s, c.val s * κ s p₀ ≠ 0 := by
    by_contra! h
    exact hp (finsum_eq_zero_of_forall_eq_zero h)
  have h₀ := hκ _ _ (right_ne_zero_of_mul hs)
  exact Set.mem_biUnion (x := s) ⟨left_ne_zero_of_mul hs, by linarith⟩
    ⟨right_ne_zero_of_mul hs, hT⟩

variable {C : ℝ} {m : S₁ → S₀ → R}
  (hm : ∀ p₁ p₀, m p₁ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + C)
  (hmfin : ∀ p₁, m p₁ ∈ NovikovModule R F₀)

include hm in
/-- For a kernel obeying a potential bound, each coefficient of the image is a sum with finitely
many nonzero terms. -/
theorem finite_support_mul_kernelMap (a : NovikovModule R F₁) (p₀ : S₀) :
    (support fun p₁ => a.val p₁ * m p₁ p₀).Finite :=
  finite_support_mul (T := F₀ p₀ - C) (fun p₁ h => by linarith [hm p₁ p₀ h]) a

/-- The linear map of completed combinations given by a kernel `m` with potential bound `C` and
completed outputs: the coefficient of `p₀` in the image of `a` is the finite sum
`∑ a(p₁) m(p₁, p₀)` over all input generators. -/
def kernelMap : NovikovModule R F₁ →ₗ[R] NovikovModule R F₀ where
  toFun a := ⟨_, finsum_mul_mem (D := C) hm hmfin a⟩
  map_add' a a' := Subtype.ext <| funext fun p₀ => by
    simp only [Submodule.coe_add, Pi.add_apply, add_mul]
    exact finsum_add_distrib (finite_support_mul_kernelMap hm a p₀)
      (finite_support_mul_kernelMap hm a' p₀)
  map_smul' c a := Subtype.ext <| funext fun p₀ => by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_finsum' _ c (finite_support_mul_kernelMap hm a p₀)]
    exact finsum_congr fun p₁ => mul_assoc _ _ _

/-- The coefficient of a generator in an image is the sum, over all input generators, of the
product of their coefficients with the kernel. -/
@[simp]
theorem kernelMap_apply_val (a : NovikovModule R F₁) (p₀ : S₀) :
    (kernelMap hm hmfin a).val p₀ = ∑ᶠ p₁, a.val p₁ * m p₁ p₀ :=
  (rfl)

/-- A coefficient of an image is a sum over any finite set containing every support generator
with nonzero kernel coefficient. -/
theorem kernelMap_apply_val_eq_sum (a : NovikovModule R F₁) (p₀ : S₀) {s : Finset S₁}
    (hs : ∀ p₁, a.val p₁ ≠ 0 → m p₁ p₀ ≠ 0 → p₁ ∈ s) :
    (kernelMap hm hmfin a).val p₀ = ∑ p₁ ∈ s, a.val p₁ * m p₁ p₀ := by
  rw [kernelMap_apply_val]
  exact finsum_eq_sum_of_support_subset _ fun p₁ hp =>
    hs p₁ (left_ne_zero_of_mul hp) (right_ne_zero_of_mul hp)

/-- The map shifts potential cutoffs by the constant of the potential bound: if `a` vanishes
above `D`, then its image vanishes above `D + C`. -/
theorem kernelMap_apply_val_eq_zero {a : NovikovModule R F₁} {D : ℝ}
    (ha : ∀ s, D < F₁ s → a.val s = 0) {p₀ : S₀} (hp : D + C < F₀ p₀) :
    (kernelMap hm hmfin a).val p₀ = 0 := by
  rw [kernelMap_apply_val]
  refine finsum_eq_zero_of_forall_eq_zero fun p₁ => ?_
  by_contra hp₁
  have h₁ : F₁ p₁ ≤ D := not_lt.1 fun h => left_ne_zero_of_mul hp₁ (ha _ h)
  have h₀ := hm _ _ (right_ne_zero_of_mul hp₁)
  linarith

/-- The map of a sum of kernels is the sum of their maps. The three potential bounds may have
different constants. -/
theorem kernelMap_add {C' C'' : ℝ} {m' : S₁ → S₀ → R}
    (hm' : ∀ p₁ p₀, m' p₁ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + C') (hmfin' : ∀ p₁, m' p₁ ∈ NovikovModule R F₀)
    (hmm' : ∀ p₁ p₀, (m + m') p₁ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + C'')
    (hmmfin' : ∀ p₁, (m + m') p₁ ∈ NovikovModule R F₀) :
    kernelMap hmm' hmmfin' = kernelMap hm hmfin + kernelMap hm' hmfin' := by
  ext a p₀
  simp only [kernelMap_apply_val, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, mul_add]
  exact finsum_add_distrib (finite_support_mul_kernelMap hm a p₀)
    (finite_support_mul_kernelMap hm' a p₀)

/-- The zero kernel gives the zero map. -/
@[simp]
theorem kernelMap_zero (hm : ∀ p₁ p₀, (0 : S₁ → S₀ → R) p₁ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + C)
    (hmfin : ∀ p₁, (0 : S₁ → S₀ → R) p₁ ∈ NovikovModule R F₀) :
    kernelMap hm hmfin = 0 := by
  ext a p₀
  simp

/-- The identity kernel, with coefficient `1` on the diagonal and `0` off it, gives the identity
map. -/
@[simp]
theorem kernelMap_eq_id {S : Type*} [DecidableEq S] {F : S → ℝ}
    (hm : ∀ p q, (if p = q then (1 : R) else 0) ≠ 0 → F q ≤ F p + C)
    (hmfin : ∀ p, (fun q => if p = q then (1 : R) else 0) ∈ NovikovModule R F) :
    kernelMap hm hmfin = LinearMap.id := by
  ext a q
  simp only [kernelMap_apply_val, LinearMap.id_apply, mul_ite, mul_one, mul_zero]
  rw [finsum_eq_single _ q fun p hp => by simp [hp]]
  simp

end Map

section Comp

variable {R S₁ S₂ S₀ : Type*} [Semiring R] {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ}

/-- The composite of a kernel `m` from `S₁` to `S₀` with a kernel `m'` from `S₀` to `S₂`: the
matrix product `∑ m(p₁, p₀) m'(p₀, p₂)` over the intermediate generators. -/
def kernelComp (m : S₁ → S₀ → R) (m' : S₀ → S₂ → R) (p₁ : S₁) (p₂ : S₂) : R :=
  ∑ᶠ p₀, m p₁ p₀ * m' p₀ p₂

/-- A coefficient of a composite kernel is the sum over intermediate generators. -/
theorem kernelComp_apply (m : S₁ → S₀ → R) (m' : S₀ → S₂ → R) (p₁ : S₁) (p₂ : S₂) :
    kernelComp m m' p₁ p₂ = ∑ᶠ p₀, m p₁ p₀ * m' p₀ p₂ :=
  (rfl)

variable {C C' : ℝ} {m : S₁ → S₀ → R} {m' : S₀ → S₂ → R}

/-- **Potential bound of a composite kernel.** If the outputs of `m` at `p₁` have potential at
most `D` and `m'` raises potentials by at most `C'`, then the outputs of the composite kernel at
`p₁` have potential at most `D + C'`. -/
theorem potential_le_of_kernelComp_ne_zero {D : ℝ} {p₁ : S₁} {p₂ : S₂}
    (hm : ∀ p₀, m p₁ p₀ ≠ 0 → F₀ p₀ ≤ D) (hm' : ∀ p₀, m' p₀ p₂ ≠ 0 → F₂ p₂ ≤ F₀ p₀ + C')
    (h : kernelComp m m' p₁ p₂ ≠ 0) : F₂ p₂ ≤ D + C' := by
  obtain ⟨p₀, hp₀⟩ : ∃ p₀, m p₁ p₀ * m' p₀ p₂ ≠ 0 := by
    by_contra! h'
    exact h (finsum_eq_zero_of_forall_eq_zero h')
  linarith [hm p₀ (left_ne_zero_of_mul hp₀), hm' p₀ (right_ne_zero_of_mul hp₀)]

/-- **Completed outputs of a composite kernel.** If the output of `m` at `p₁` is a completed
combination and `m'` is supported, then the output of the composite kernel at `p₁` is a completed
combination. -/
theorem kernelComp_mem (hm' : ∀ p₀ p₂, m' p₀ p₂ ≠ 0 → F₂ p₂ ≤ F₀ p₀ + C')
    (hmfin' : ∀ p₀, m' p₀ ∈ NovikovModule R F₂) {p₁ : S₁} (hmfin : m p₁ ∈ NovikovModule R F₀) :
    kernelComp m m' p₁ ∈ NovikovModule R F₂ :=
  finsum_mul_mem hm' hmfin' ⟨m p₁, hmfin⟩

variable (hm : ∀ p₁ p₀, m p₁ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + C)
  (hmfin : ∀ p₁, m p₁ ∈ NovikovModule R F₀)
  (hm' : ∀ p₀ p₂, m' p₀ p₂ ≠ 0 → F₂ p₂ ≤ F₀ p₀ + C')
  (hmfin' : ∀ p₀, m' p₀ ∈ NovikovModule R F₂)

include hm hmfin hm' in
/-- For a completed combination `a`, only finitely many pairs of an input generator and an
intermediate generator contribute to a coefficient of the image of `a` under a composite. -/
private theorem finite_support_mul_mul (a : NovikovModule R F₁) (p₂ : S₂) :
    (support fun x : S₀ × S₁ => a.val x.2 * m x.2 x.1 * m' x.1 p₂).Finite := by
  refine ((finite_ge a (F₂ p₂ - C' - C)).biUnion fun p₁ _ =>
    (finite_ge ⟨m p₁, hmfin p₁⟩ (F₂ p₂ - C')).image fun p₀ => (p₀, p₁)).subset ?_
  rintro ⟨p₀, p₁⟩ hx
  have ha := left_ne_zero_of_mul (left_ne_zero_of_mul hx)
  have h₁ := hm _ _ (right_ne_zero_of_mul (left_ne_zero_of_mul hx))
  have h₂ := hm' _ _ (right_ne_zero_of_mul hx)
  exact Set.mem_biUnion (x := p₁) ⟨ha, by linarith⟩
    ⟨p₀, ⟨right_ne_zero_of_mul (left_ne_zero_of_mul hx), by linarith⟩, rfl⟩

/-- **Composition of kernel maps.** Applying the maps of `m` and then of `m'` is the map of the
composite kernel. The potential bound of the composite may have any constant. -/
theorem kernelMap_kernelMap {C'' : ℝ}
    (hmm' : ∀ p₁ p₂, kernelComp m m' p₁ p₂ ≠ 0 → F₂ p₂ ≤ F₁ p₁ + C'')
    (hmmfin' : ∀ p₁, kernelComp m m' p₁ ∈ NovikovModule R F₂) (a : NovikovModule R F₁) :
    kernelMap hm' hmfin' (kernelMap hm hmfin a) = kernelMap hmm' hmmfin' a := by
  ext p₂
  simp only [kernelMap_apply_val, kernelComp_apply]
  calc
    ∑ᶠ p₀, (∑ᶠ p₁, a.val p₁ * m p₁ p₀) * m' p₀ p₂ =
        ∑ᶠ p₀, ∑ᶠ p₁, a.val p₁ * m p₁ p₀ * m' p₀ p₂ :=
      finsum_congr fun p₀ => finsum_mul' _ _ (finite_support_mul_kernelMap hm a p₀)
    _ = ∑ᶠ p₁, ∑ᶠ p₀, a.val p₁ * m p₁ p₀ * m' p₀ p₂ :=
      finsum_comm (finite_support_mul_mul hm hmfin hm' a p₂)
    _ = ∑ᶠ p₁, a.val p₁ * ∑ᶠ p₀, m p₁ p₀ * m' p₀ p₂ := finsum_congr fun p₁ => by
      rw [mul_finsum' _ _ (finite_support_mul_kernelMap hm' ⟨m p₁, hmfin p₁⟩ p₂)]
      exact finsum_congr fun p₀ => mul_assoc _ _ _

/-- **Composition of kernel maps**, as an equation of linear maps. -/
theorem kernelMap_comp {C'' : ℝ}
    (hmm' : ∀ p₁ p₂, kernelComp m m' p₁ p₂ ≠ 0 → F₂ p₂ ≤ F₁ p₁ + C'')
    (hmmfin' : ∀ p₁, kernelComp m m' p₁ ∈ NovikovModule R F₂) :
    kernelMap hm' hmfin' ∘ₗ kernelMap hm hmfin = kernelMap hmm' hmmfin' :=
  LinearMap.ext (kernelMap_kernelMap hm hmfin hm' hmfin' hmm' hmmfin')

end Comp

section Torsor

variable {R H ι₁ ι₀ : Type*} [Semiring R] [AddGroup H] {N : H →+ ℝ}
  {P₁ : ι₁ → Type*} {P₀ : ι₀ → Type*} [∀ i, AddTorsor H (P₁ i)] [∀ k, AddTorsor H (P₀ k)]
  {F₁ : (Σ i, P₁ i) → ℝ} {F₀ : (Σ k, P₀ k) → ℝ}
  (hF₁ : ∀ i h (p : P₁ i), F₁ ⟨i, h +ᵥ p⟩ = F₁ ⟨i, p⟩ - N h)
  (hF₀ : ∀ k h (p : P₀ k), F₀ ⟨k, h +ᵥ p⟩ = F₀ ⟨k, p⟩ - N h)

/-- In lift coordinates, a completed combination given by an invariant one-input kernel `m`,
`c(p₀) = ∑ a(p₁) m(p₁, p₀)`, is given by the matrix of Novikov series of `m` in the reference
generators: `cₖ = ∑ᵢ aᵢ Mᵢₖ`. -/
theorem coordinates_eq_sum_mul [Fintype ι₁] [Finite ι₀]
    {m : (Σ i, P₁ i) → (Σ k, P₀ k) → R} (hmfin : ∀ p₁, m p₁ ∈ NovikovModule R F₀)
    (hm : ∀ (g : H) i (p₁ : P₁ i) k (p₀ : P₀ k), m ⟨i, g +ᵥ p₁⟩ ⟨k, g +ᵥ p₀⟩ = m ⟨i, p₁⟩ ⟨k, p₀⟩)
    (r₁ : ∀ i, P₁ i) (r₀ : ∀ k, P₀ k) {a : NovikovModule R F₁} {c : NovikovModule R F₀}
    (hc : ∀ p₀, c.val p₀ = ∑ᶠ p₁, a.val p₁ * m p₁ p₀) (k : ι₀) :
    coordinates hF₀ r₀ c k =
      ∑ i, coordinates hF₁ r₁ a i * coordinates hF₀ r₀ ⟨m ⟨i, r₁ i⟩, hmfin _⟩ k := by
  classical
  -- The pairs of exponents contributing to the coefficient at `h` on the right are sent
  -- injectively by `g` onto input generators covering the support of the left side, and
  -- invariance of the kernel matches the summands.
  ext h
  set x := coordinates hF₁ r₁ a
  set M : ι₁ → NovikovSeries R H N := fun i => coordinates hF₀ r₀ ⟨m ⟨i, r₁ i⟩, hmfin _⟩ k
  have hM (i : ι₁) (v : H) : (M i).coeff v = m ⟨i, r₁ i⟩ ⟨k, v +ᵥ r₀ k⟩ :=
    coordinates_coeff hF₀ r₀ _ k v
  let T : ι₁ → Finset (H × H) := fun i =>
    (NovikovSeries.finite_setOf_add_eq (x i) (M i) h).toFinset
  have hT (i : ι₁) (t : H × H) :
      t ∈ T i ↔ t.1 + t.2 = h ∧ (x i).coeff t.1 ≠ 0 ∧ (M i).coeff t.2 ≠ 0 :=
    Set.Finite.mem_toFinset _
  let g : (Σ _ : ι₁, H × H) → Σ i, P₁ i := fun u => ⟨u.1, u.2.1 +ᵥ r₁ u.1⟩
  have hR : (∑ i, x i * M i).coeff h =
      ∑ u ∈ Finset.univ.sigma T, (x u.1).coeff u.2.1 * (M u.1).coeff u.2.2 := by
    rw [Finset.sum_sigma]
    simp only [NovikovSeries.coeff_sum, NovikovSeries.coeff_mul, T]
  have hs : (support fun p₁ => a.val p₁ * m p₁ ⟨k, h +ᵥ r₀ k⟩) ⊆
      ↑((Finset.univ.sigma T).image g) := by
    rintro ⟨i, p⟩ hp
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨⟨i, (p -ᵥ r₁ i, -(p -ᵥ r₁ i) + h)⟩,
      Finset.mem_sigma.2 ⟨Finset.mem_univ _, (hT _ _).2 ⟨add_neg_cancel_left _ _, ?_, ?_⟩⟩, ?_⟩)
    · simpa [x] using left_ne_zero_of_mul hp
    · rw [hM, ← hm (p -ᵥ r₁ i), vsub_vadd, ← add_vadd, add_neg_cancel_left]
      exact right_ne_zero_of_mul hp
    · simp [g]
  have hinj : Set.InjOn g (Finset.univ.sigma T) := by
    rintro ⟨i, ⟨u, v⟩⟩ hu ⟨i', ⟨u', v'⟩⟩ hu' he
    simp only [g, Sigma.mk.inj_iff] at he
    obtain ⟨rfl, e⟩ := he
    obtain rfl := vadd_right_injective _ (eq_of_heq e)
    have s := ((hT _ _).1 (Finset.mem_sigma.1 hu).2).1
    have s' := ((hT _ _).1 (Finset.mem_sigma.1 hu').2).1
    obtain rfl : v = v' := add_left_cancel (s.trans s'.symm)
    rfl
  rw [coordinates_coeff, hc, finsum_eq_sum_of_support_subset _ hs, Finset.sum_image hinj, hR]
  refine Finset.sum_congr rfl fun u hu => ?_
  obtain ⟨i, ⟨u, v⟩⟩ := u
  have s := ((hT _ _).1 (Finset.mem_sigma.1 hu).2).1
  rw [hM, ← hm u i (r₁ i) k (v +ᵥ r₀ k), ← add_vadd, s]
  simp only [g, x, coordinates_coeff]

variable {C : ℝ} {m : (Σ i, P₁ i) → (Σ k, P₀ k) → R}
  (hm : ∀ p₁ p₀, m p₁ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + C)
  (hmfin : ∀ p₁, m p₁ ∈ NovikovModule R F₀)
  (hminv : ∀ (g : H) i (p₁ : P₁ i) k (p₀ : P₀ k),
    m ⟨i, g +ᵥ p₁⟩ ⟨k, g +ᵥ p₀⟩ = m ⟨i, p₁⟩ ⟨k, p₀⟩)

include hminv in
/-- **The matrix of an invariant kernel map.** In lift coordinates, the map of an invariant
kernel is multiplication by the matrix whose `(i, k)` entry is the Novikov series of coordinates,
in the orbit `k`, of the output of `m` at the reference generator of the orbit `i`. -/
theorem coordinates_kernelMap [Fintype ι₁] [Finite ι₀] (r₁ : ∀ i, P₁ i) (r₀ : ∀ k, P₀ k)
    (a : NovikovModule R F₁) (k : ι₀) :
    coordinates hF₀ r₀ (kernelMap hm hmfin a) k =
      ∑ i, coordinates hF₁ r₁ a i * coordinates hF₀ r₀ ⟨m ⟨i, r₁ i⟩, hmfin _⟩ k :=
  coordinates_eq_sum_mul hF₁ hF₀ hmfin hminv r₁ r₀ (fun _ => rfl) k

include hminv in
/-- The map of an invariant kernel is linear over the Novikov ring, for the Novikov module
structures of `TauCeti.NovikovModule.module`. -/
theorem kernelMap_smul [Finite ι₁] [Finite ι₀] (β : NovikovSeries R H N)
    (a : NovikovModule R F₁) :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₀
    kernelMap hm hmfin (β • a) = β • kernelMap hm hmfin a := by
  let := module (R := R) hF₁
  let := module (R := R) hF₀
  have := Fintype.ofFinite ι₁
  let r₁ := fun i => Classical.arbitrary (P₁ i)
  let r₀ := fun k => Classical.arbitrary (P₀ k)
  refine (coordinates hF₀ r₀).injective (funext fun k => ?_)
  rw [coordinates_smul, Pi.smul_apply, coordinates_kernelMap hF₁ hF₀ hm hmfin hminv r₁ r₀,
    coordinates_kernelMap hF₁ hF₀ hm hmfin hminv r₁ r₀, coordinates_smul]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- The map of an invariant kernel, as a linear map over the Novikov ring, for the Novikov module
structures of `TauCeti.NovikovModule.module`. -/
def novikovKernelMap [Finite ι₁] [Finite ι₀] :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₀
    NovikovModule R F₁ →ₗ[NovikovSeries R H N] NovikovModule R F₀ :=
  letI := module (R := R) hF₁
  letI := module (R := R) hF₀
  { toFun := kernelMap hm hmfin
    map_add' := map_add _
    map_smul' := kernelMap_smul hF₁ hF₀ hm hmfin hminv }

/-- The Novikov-linear map evaluates to the map of the kernel. -/
@[simp]
theorem novikovKernelMap_apply [Finite ι₁] [Finite ι₀] (a : NovikovModule R F₁) :
    novikovKernelMap hF₁ hF₀ hm hmfin hminv a = kernelMap hm hmfin a :=
  (rfl)

end Torsor

end NovikovModule

end TauCeti
