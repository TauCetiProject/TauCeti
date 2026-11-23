/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Geometry.Manifold.GroupLieAlgebra
public import Mathlib.RepresentationTheory.Continuous.Basic
public import TauCeti.Geometry.Lie.InvariantVectorField.Basic

/-!
# Smooth vectors of representations of Lie groups and their seminorms

Let `π` be a representation of a real Lie group `G` on a normed space `V` by continuous linear
operators. A vector `v` is *smooth* (`ContRepresentation.IsLieSmoothVector`) when its orbit map
`g ↦ π g v` is smooth. The smooth vectors form a `G`-invariant subspace
`ContRepresentation.lieSmoothVectors`.

For `X` in the Lie algebra `GroupLieAlgebra I G` (the tangent space at the identity), the
*derived action* `dπ(X) v` is the derivative of the orbit map of `v` at the identity in the
direction `X`. Translating by `π g` turns it into the derivative of the orbit map at `g` along
the left-invariant vector field of `X` (`ContRepresentation.apply_derivedApply`), and so `dπ(X)`
maps smooth vectors to smooth vectors (`ContRepresentation.derivedAction`).

Fix a family `X : ι → GroupLieAlgebra I G` of Lie algebra elements, for instance a basis. For a
word `w = i₁ ⋯ iₙ` in `ι` write `dπ(X_w) = dπ(X_{i₁}) ∘ ⋯ ∘ dπ(X_{iₙ})`. The *word seminorm*
of order `k` is

`P_k(v) = ∑_{|w| ≤ k} ‖dπ(X_w) v‖`,

summed over all words of length at most `k`. For `ι = Fin m` the *Sobolev seminorm* of order `k`
(Bernstein–Krötz) uses only the ordered monomials `X^α = X₁^{α₁} ⋯ X_m^{α_m}`:

`Q_k(v) = (∑_{|α| ≤ k} ‖dπ(X^α) v‖²)^{1/2}`.

Every ordered monomial is a word, so `Q_k ≤ P_k` (`ContRepresentation.sobolevSeminorm_le`).

## Main definitions

* `ContRepresentation.IsLieSmoothVector I π v`: the orbit map of `v` is smooth.
* `ContRepresentation.lieSmoothVectors I π`: the submodule of smooth vectors.
* `ContRepresentation.derivedApply I π X v`: the derivative `dπ(X) v` of the orbit map of `v` at
  the identity in the direction `X`.
* `ContRepresentation.derivedAction π X`: `dπ(X)` as a linear operator on smooth vectors.
* `ContRepresentation.wordAction π X w`: the operator `dπ(X_w)` of a word `w`.
* `ContRepresentation.Word ι k`: the words in `ι` of length at most `k`.
* `ContRepresentation.wordSeminorm π X k`: the word seminorm `P_k`.
* `ContRepresentation.monomialWord α`: the word `1^{α₁} ⋯ m^{α_m}` of an exponent vector.
* `ContRepresentation.SobolevIndex m k`: the exponent vectors `α : Fin m → ℕ` with `|α| ≤ k`.
* `ContRepresentation.sobolevSeminorm π X k`: the Sobolev seminorm `Q_k`.

## Main results

* `ContRepresentation.isLieSmoothVector_apply`, `ContRepresentation.apply_mem_lieSmoothVectors`:
  `π g` maps smooth vectors to smooth vectors.
* `ContRepresentation.apply_derivedApply`: `π g (dπ(X) v)` is the derivative of the orbit map of
  `v` at `g` along the left-invariant vector field of `X`.
* `ContRepresentation.isLieSmoothVector_derivedApply`: `dπ(X)` preserves smooth vectors.
* `ContRepresentation.wordSeminorm_apply`, `ContRepresentation.sobolevSeminorm_apply`: the two
  seminorms as explicit sums.
* `ContRepresentation.wordSeminorm_zero`: `P_0` is the norm.
* `ContRepresentation.sobolevSeminorm_le`: `Q_k ≤ P_k`.

## References

* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*,
  Israel J. Math. 199 (2014), §§2.1–2.4.
-/

@[expose] public section

noncomputable section

open scoped ContDiff Manifold

namespace ContRepresentation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V]
  (π : ContRepresentation 𝕜 G V)

/-! ### Smooth vectors -/

/-- A vector `v` is smooth for a representation `π` of a Lie group when its orbit map
`g ↦ π g v` is smooth. -/
def IsLieSmoothVector (v : V) : Prop :=
  ContMDiff I 𝓘(ℝ, V) ∞ (fun g : G ↦ π g v)

variable {I π}

/-- The zero vector is smooth. -/
theorem isLieSmoothVector_zero : IsLieSmoothVector I π 0 := by
  simpa [IsLieSmoothVector] using contMDiff_const (c := (0 : V))

/-- A sum of smooth vectors is smooth. -/
theorem IsLieSmoothVector.add {v w : V} (hv : IsLieSmoothVector I π v)
    (hw : IsLieSmoothVector I π w) : IsLieSmoothVector I π (v + w) := by
  simp only [IsLieSmoothVector, map_add]
  exact ContMDiff.add hv hw

/-- Each operator `π h` maps smooth vectors to smooth vectors: the orbit map of `π h v` is that
of `v` precomposed with right multiplication by `h`. -/
theorem isLieSmoothVector_apply [ContMDiffMul I ∞ G] {v : V} (hv : IsLieSmoothVector I π v)
    (h : G) : IsLieSmoothVector I π (π h v) := by
  have : ContMDiff I 𝓘(ℝ, V) ∞ (fun g : G ↦ π (g * h) v) :=
    ContMDiff.comp (I' := I) hv contMDiff_mul_right
  simpa [IsLieSmoothVector, map_mul] using this

private theorem IsLieSmoothVector.mdifferentiable {v : V} (hv : IsLieSmoothVector I π v) :
    MDifferentiable I 𝓘(ℝ, V) (fun g : G ↦ π g v) :=
  ContMDiff.mdifferentiable hv (by simp)

/-! ### The derived action -/

variable (I π) in
/-- The derived action `dπ(X) v`: the derivative at the identity of the orbit map `g ↦ π g v`,
in the direction `X` of the Lie algebra. -/
def derivedApply (X : GroupLieAlgebra I G) (v : V) : V :=
  mvfderiv I (fun g : G ↦ π g v) 1 X

/-- `dπ(X) v` is additive in `X`. -/
theorem derivedApply_add_left (X Y : GroupLieAlgebra I G) (v : V) :
    derivedApply I π (X + Y) v = derivedApply I π X v + derivedApply I π Y v :=
  map_add _ X Y

/-- `dπ(X) v` is real-homogeneous in `X`. -/
theorem derivedApply_smul_left (c : ℝ) (X : GroupLieAlgebra I G) (v : V) :
    derivedApply I π (c • X) v = c • derivedApply I π X v :=
  map_smul _ c X

/-- `dπ(X)` is additive on smooth vectors. -/
theorem derivedApply_add {v w : V} (hv : IsLieSmoothVector I π v) (hw : IsLieSmoothVector I π w)
    (X : GroupLieAlgebra I G) :
    derivedApply I π X (v + w) = derivedApply I π X v + derivedApply I π X w := by
  simp only [derivedApply, map_add]
  change mvfderiv I ((fun g : G ↦ π g v) + fun g : G ↦ π g w) 1 X = _
  rw [mvfderiv_add (hv.mdifferentiable 1) (hw.mdifferentiable 1)]
  rfl

omit [Group G] in
private theorem mvfderiv_clm_comp (L : V →L[ℝ] V) {f : G → V} {x : G}
    (hf : MDifferentiableAt I 𝓘(ℝ, V) f x) :
    mvfderiv I (fun g ↦ L (f g)) x = L ∘L mvfderiv I f x := by
  have h := mvfderiv_comp (g := L) (f := f) x L.mdifferentiableAt hf
  rw [show (fun g ↦ L (f g)) = L ∘ f from rfl, h, mvfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  rfl

section Scalars

variable [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 V]

/-- A continuous `𝕜`-linear operator, as a continuous `ℝ`-linear operator. -/
private abbrev realCLM (L : V →L[𝕜] V) : V →L[ℝ] V := L.restrictScalars ℝ

/-- A scalar multiple of a smooth vector is smooth. -/
theorem IsLieSmoothVector.smul {v : V} (hv : IsLieSmoothVector I π v) (c : 𝕜) :
    IsLieSmoothVector I π (c • v) := by
  have : ContMDiff I 𝓘(ℝ, V) ∞ (fun g : G ↦ realCLM (c • ContinuousLinearMap.id 𝕜 V) (π g v)) :=
    (realCLM (c • ContinuousLinearMap.id 𝕜 V)).contMDiff.comp hv
  simpa [IsLieSmoothVector] using this

variable (I π) in
/-- The submodule of smooth vectors of a representation of a Lie group. -/
def lieSmoothVectors : Submodule 𝕜 V where
  carrier := {v | IsLieSmoothVector I π v}
  add_mem' := IsLieSmoothVector.add
  zero_mem' := isLieSmoothVector_zero
  smul_mem' c _ hv := hv.smul c

/-- Membership in the smooth vectors. -/
@[simp]
theorem mem_lieSmoothVectors {v : V} : v ∈ lieSmoothVectors I π ↔ IsLieSmoothVector I π v :=
  Iff.rfl

/-- `π h` maps the smooth vectors into themselves. -/
theorem apply_mem_lieSmoothVectors [ContMDiffMul I ∞ G] {v : V} (hv : v ∈ lieSmoothVectors I π)
    (h : G) : π h v ∈ lieSmoothVectors I π :=
  isLieSmoothVector_apply hv h

/-- `dπ(X)` is `𝕜`-homogeneous on smooth vectors. -/
theorem derivedApply_smul {v : V} (hv : IsLieSmoothVector I π v) (c : 𝕜)
    (X : GroupLieAlgebra I G) : derivedApply I π X (c • v) = c • derivedApply I π X v := by
  have h := mvfderiv_clm_comp (realCLM (c • ContinuousLinearMap.id 𝕜 V)) (hv.mdifferentiable 1)
  simp only [derivedApply, map_smul]
  exact congrArg (fun L ↦ L X) h

variable [ContMDiffMul I ∞ G]

/-- Translating `dπ(X) v` by `π g` gives the derivative of the orbit map of `v` at `g` along the
left-invariant vector field of `X`. -/
theorem apply_derivedApply {v : V} (hv : IsLieSmoothVector I π v) (X : GroupLieAlgebra I G)
    (g : G) :
    π g (derivedApply I π X v) =
      mvfderiv I (fun h : G ↦ π h v) g (mulInvariantVectorField X g) := by
  have hL : (fun h : G ↦ π (g * h) v) = (fun h : G ↦ π h v) ∘ (g * ·) := rfl
  have h₁ : mvfderiv I (fun h : G ↦ π (g * h) v) 1 X =
      mvfderiv I (fun h : G ↦ π h v) g (mulInvariantVectorField X g) := by
    rw [hL, mvfderiv_comp_apply_of_eq (y := g) 1 (hv.mdifferentiable g)
      (mdifferentiableAt_mul_left (a := g)) (by simp)]
    rfl
  have h₂ : mvfderiv I (fun h : G ↦ π (g * h) v) 1 =
      realCLM (π g) ∘L mvfderiv I (fun h : G ↦ π h v) 1 := by
    simp_rw [map_mul, mul_apply_eq_comp]
    exact mvfderiv_clm_comp (realCLM (π g)) (hv.mdifferentiable 1)
  rw [← h₁, h₂]
  rfl

/-- The derived action maps smooth vectors to smooth vectors. -/
theorem isLieSmoothVector_derivedApply {v : V} (hv : IsLieSmoothVector I π v)
    (X : GroupLieAlgebra I G) : IsLieSmoothVector I π (derivedApply I π X v) := by
  have : ContMDiff I 𝓘(ℝ, V) ∞
      (fun g : G ↦ mvfderiv I (fun h : G ↦ π h v) g (mulInvariantVectorField X g)) :=
    ContMDiff.mvfderiv hv (contMDiff_mulInvariantVectorField_infty X) (by simp)
  simpa [IsLieSmoothVector, apply_derivedApply hv] using this

variable (π) in
/-- The derived action `dπ(X)` as a linear operator on the smooth vectors. -/
def derivedAction (X : GroupLieAlgebra I G) : Module.End 𝕜 (lieSmoothVectors I π) where
  toFun v := ⟨derivedApply I π X v, isLieSmoothVector_derivedApply v.property X⟩
  map_add' v w := Subtype.ext (derivedApply_add v.property w.property X)
  map_smul' c v := Subtype.ext (derivedApply_smul v.property c X)

/-- The value of `dπ(X)` on a smooth vector. -/
@[simp]
theorem coe_derivedAction_apply (X : GroupLieAlgebra I G) (v : lieSmoothVectors I π) :
    (derivedAction π X v : V) = derivedApply I π X v :=
  rfl

/-! ### Words and the word seminorms -/

variable {ι : Type*}

variable (π) in
/-- The operator `dπ(X_w) = dπ(X_{i₁}) ∘ ⋯ ∘ dπ(X_{iₙ})` on smooth vectors attached to a word
`w = [i₁, …, iₙ]`. -/
def wordAction (X : ι → GroupLieAlgebra I G) (w : List ι) : Module.End 𝕜 (lieSmoothVectors I π) :=
  (w.map fun i ↦ derivedAction π (X i)).prod

/-- The empty word acts as the identity. -/
@[simp]
theorem wordAction_nil (X : ι → GroupLieAlgebra I G) : wordAction π X [] = 1 :=
  rfl

/-- `dπ(X_{i w}) = dπ(X_i) ∘ dπ(X_w)`. -/
@[simp]
theorem wordAction_cons (X : ι → GroupLieAlgebra I G) (i : ι) (w : List ι) :
    wordAction π X (i :: w) = derivedAction π (X i) * wordAction π X w :=
  rfl

/-- The words in `ι` of length at most `k`: a word of length `n ≤ k` is `⟨n, w⟩` with
`w : Fin n → ι`. -/
abbrev Word (ι : Type*) (k : ℕ) : Type _ :=
  Σ n : Fin (k + 1), Fin n → ι

variable [Fintype ι]

variable (π) in
/-- The word seminorm `P_k(v) = ∑_{|w| ≤ k} ‖dπ(X_w) v‖` on smooth vectors, summed over all
words `w` in `ι` of length at most `k`. -/
def wordSeminorm (X : ι → GroupLieAlgebra I G) (k : ℕ) : Seminorm 𝕜 (lieSmoothVectors I π) :=
  ∑ w : Word ι k,
    (normSeminorm 𝕜 V).comp ((lieSmoothVectors I π).subtype ∘ₗ wordAction π X (List.ofFn w.2))

/-- The word seminorm as an explicit sum over words. -/
theorem wordSeminorm_apply (X : ι → GroupLieAlgebra I G) (k : ℕ) (v : lieSmoothVectors I π) :
    wordSeminorm π X k v = ∑ w : Word ι k, ‖(wordAction π X (List.ofFn w.2) v : V)‖ := by
  change FunLike.coeAddMonoidHom _ _ _ (wordSeminorm π X k) v = _
  simp [wordSeminorm, map_sum, Finset.sum_apply]

/-- The word seminorm of order zero is the norm of `V`. -/
@[simp]
theorem wordSeminorm_zero (X : ι → GroupLieAlgebra I G) (v : lieSmoothVectors I π) :
    wordSeminorm π X 0 v = ‖(v : V)‖ := by
  rw [wordSeminorm_apply, Fintype.sum_eq_single ⟨0, Fin.elim0⟩]
  · simp
  · rintro ⟨n, w⟩ h
    refine absurd ?_ h
    obtain rfl : n = 0 := Fin.ext (Nat.lt_one_iff.mp n.isLt)
    exact Sigma.ext rfl (heq_of_eq (funext fun i ↦ i.elim0))

/-! ### Ordered monomials and the Sobolev seminorms -/

variable {m : ℕ}

/-- The ordered monomial word `1^{α₁} 2^{α₂} ⋯ m^{α_m}` of an exponent vector `α`. -/
def monomialWord (α : Fin m → ℕ) : List (Fin m) :=
  (List.finRange m).flatMap fun i ↦ List.replicate (α i) i

/-- The ordered monomial word of `α` has length `|α|`. -/
theorem length_monomialWord (α : Fin m → ℕ) : (monomialWord α).length = ∑ i, α i := by
  simp [monomialWord, List.length_flatMap, Fin.sum_univ_def]

/-- The letter `i` occurs `α i` times in the ordered monomial word of `α`. -/
theorem count_monomialWord (α : Fin m → ℕ) (i : Fin m) : (monomialWord α).count i = α i := by
  rw [monomialWord, List.count_flatMap, ← Fin.sum_univ_def]
  simp [List.count_replicate]

/-- An ordered monomial word determines its exponent vector. -/
theorem monomialWord_injective : Function.Injective (monomialWord (m := m)) := fun α β h ↦
  funext fun i ↦ by rw [← count_monomialWord α i, ← count_monomialWord β i, h]

/-- The exponent vectors `α : Fin m → ℕ` of total degree `|α| = ∑ i, α i ≤ k`, with entries
recorded in `Fin (k + 1)` so that they form a finite type. -/
abbrev SobolevIndex (m k : ℕ) : Type :=
  {α : Fin m → Fin (k + 1) // ∑ i, (α i : ℕ) ≤ k}

/-- The exponent vector in `ℕ` of an index in `SobolevIndex m k`. -/
def SobolevIndex.exponent {k : ℕ} (α : SobolevIndex m k) (i : Fin m) : ℕ :=
  α.val i

/-- An index in `SobolevIndex m k` is determined by its exponent vector. -/
theorem SobolevIndex.exponent_injective {k : ℕ} :
    Function.Injective (SobolevIndex.exponent (m := m) (k := k)) := fun _ _ h ↦
  Subtype.ext (funext fun i ↦ Fin.ext (congrFun h i))

/-- The ordered monomial word of an index in `SobolevIndex m k`, as a word of length at most
`k`. -/
def SobolevIndex.toWord {k : ℕ} (α : SobolevIndex m k) : Word (Fin m) k :=
  ⟨⟨(monomialWord α.exponent).length, by
      rw [length_monomialWord]; exact Nat.lt_succ_of_le α.property⟩,
    (monomialWord α.exponent).get⟩

/-- `SobolevIndex.toWord α` spells the ordered monomial word of `α`. -/
theorem SobolevIndex.ofFn_toWord {k : ℕ} (α : SobolevIndex m k) :
    List.ofFn α.toWord.2 = monomialWord α.exponent :=
  List.ofFn_get _

/-- Distinct ordered monomials give distinct words. -/
theorem SobolevIndex.toWord_injective {k : ℕ} :
    Function.Injective (SobolevIndex.toWord (m := m) (k := k)) := fun α β h ↦ by
  have := congrArg (fun w : Word (Fin m) k ↦ List.ofFn w.2) h
  simp only [SobolevIndex.ofFn_toWord] at this
  exact SobolevIndex.exponent_injective (monomialWord_injective this)

variable (π) in
/-- The vector `(dπ(X^α) v)_{|α| ≤ k}` of ordered monomial derivatives, in the `ℓ²` product. -/
def sobolevVector (X : Fin m → GroupLieAlgebra I G) (k : ℕ) :
    lieSmoothVectors I π →ₗ[𝕜] PiLp 2 (fun _ : SobolevIndex m k ↦ V) :=
  (WithLp.linearEquiv 2 𝕜 _).symm.toLinearMap ∘ₗ
    LinearMap.pi fun α ↦ (lieSmoothVectors I π).subtype ∘ₗ wordAction π X (monomialWord α.exponent)

variable (π) in
/-- The Sobolev seminorm `Q_k(v) = (∑_{|α| ≤ k} ‖dπ(X^α) v‖²)^{1/2}` of Bernstein–Krötz, over
the ordered monomials `X^α = X₁^{α₁} ⋯ X_m^{α_m}` of degree at most `k`. -/
def sobolevSeminorm (X : Fin m → GroupLieAlgebra I G) (k : ℕ) :
    Seminorm 𝕜 (lieSmoothVectors I π) :=
  (normSeminorm 𝕜 (PiLp 2 fun _ : SobolevIndex m k ↦ V)).comp (sobolevVector π X k)

/-- The Sobolev seminorm as an explicit square root of a sum of squares. -/
theorem sobolevSeminorm_apply (X : Fin m → GroupLieAlgebra I G) (k : ℕ)
    (v : lieSmoothVectors I π) :
    sobolevSeminorm π X k v =
      √(∑ α : SobolevIndex m k, ‖(wordAction π X (monomialWord α.exponent) v : V)‖ ^ 2) := by
  simp [sobolevSeminorm, sobolevVector, PiLp.norm_eq_of_L2]

/-- The Sobolev seminorm is bounded by the word seminorm: every ordered monomial is a word, and
the `ℓ²` norm of a finite family is at most its `ℓ¹` norm. -/
theorem sobolevSeminorm_le (X : Fin m → GroupLieAlgebra I G) (k : ℕ)
    (v : lieSmoothVectors I π) : sobolevSeminorm π X k v ≤ wordSeminorm π X k v := by
  classical
  set b : Word (Fin m) k → ℝ := fun w ↦ ‖(wordAction π X (List.ofFn w.2) v : V)‖
  have hb : ∀ α : SobolevIndex m k,
      ‖(wordAction π X (monomialWord α.exponent) v : V)‖ = b α.toWord := fun α ↦ by
    simp only [b, SobolevIndex.ofFn_toWord]
  have hsum : ∑ α : SobolevIndex m k, b α.toWord ≤ ∑ w, b w := by
    rw [← Finset.sum_image fun _ _ _ _ h ↦ SobolevIndex.toWord_injective h]
    exact Finset.sum_le_univ_sum_of_nonneg fun _ ↦ norm_nonneg _
  rw [sobolevSeminorm_apply, wordSeminorm_apply, Real.sqrt_le_iff]
  refine ⟨Finset.sum_nonneg fun _ _ ↦ norm_nonneg _, ?_⟩
  simp_rw [hb]
  calc ∑ α : SobolevIndex m k, b α.toWord ^ 2 ≤ (∑ α : SobolevIndex m k, b α.toWord) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ ↦ norm_nonneg _
    _ ≤ (∑ w, b w) ^ 2 := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) hsum 2

end Scalars

end ContRepresentation
