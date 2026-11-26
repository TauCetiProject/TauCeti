/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Isomorphisms
public import TauCeti.LinearAlgebra.Projectivization.Basic

import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Projectivization.Independence
import TauCeti.LinearAlgebra.Pi

/-!
# The line through two points, marked at its point on a hyperplane

Let `V` be a vector space over a field `K`, let `H = ℙ(ker φ)` be the hyperplane of a linear form
`φ` on `V`, and let `p ≠ q` be two points of `ℙ(V)` off `H`. A line of `ℙ(V)` with three marked
points is the image of the projective line `ℙ¹ = ℙ(K²)` under the map `[x] ↦ [A x]` of an
injective linear map `A : K² → V` (`Projectivization.map`), marked at the images of
`0 = [0 : 1]`, `1 = [1 : 1]` and `∞ = [1 : 0]`, the points `[t : 1]` of the affine coordinate `t`
at `t = 0, 1, ∞`. This file proves that **exactly one** such marked line has its first marked point
on `H`, its second at `p` and its third at `q` (`TauCeti.existsUnique_markedLine`): the line
through `p` and `q`, marked at its point on `H`. Over `ℂ`, with `V = ℂⁿ⁺¹`, the maps
`[x] ↦ [A x]` are the degree-one holomorphic maps `ℂℙ¹ → ℂℙⁿ`, and the statement says that among
the three-pointed lines of `ℂℙⁿ` with an irreducible domain exactly one is sent to
`H × {p} × {q}` by the evaluation map. This is the enumerative content of the three-point count
`⟨x, xⁿ, xⁿ⟩_L = 1` of a hyperplane class and two point classes in the class `L` of a line.

The three incidence conditions are linear in the homogeneous coordinates `A` of the marked line.
For representatives `v` of `p` and `w` of `q` they are the vanishing of the **incidence map**
(`TauCeti.markedLineIncidence φ v w`)

`A ↦ (φ (A [0 : 1]), A [1 : 1] mod K v, A [1 : 0] mod K w) : Hom(K², V) → K × V/Kv × V/Kw`,

whose three components are the conditions `[A [0 : 1]] ∈ H`, `[A [1 : 1]] = p` and
`[A [1 : 0]] = q`. Solving them gives the explicit **marked line** (`TauCeti.markedLine φ v w`)

`(x₀, x₁) ↦ x₀ φ(v) w + x₁ (φ(w) v - φ(v) w)`,

which, when `φ v ≠ 0` and `φ w ≠ 0`, sends `[1 : 0]` to `[φ(v) w] = [w]`, `[1 : 1]` to
`[φ(w) v] = [v]` and `[0 : 1]` to the point `[φ(w) v - φ(v) w]` of the line `[v] [w]` on `H`.

* **The solutions.** As soon as `φ v ≠ 0`, the kernel of the incidence map is the line spanned by
  the marked line (`TauCeti.ker_markedLineIncidence`). The marked line is injective when `v` and
  `w` are linearly independent and off `H` (`TauCeti.markedLine_injective`), and then so is every
  nonzero solution (`TauCeti.injective_of_mem_ker_markedLineIncidence`), so it defines a marked
  line of `ℙ(V)`.
* **Transversality.** As soon as `φ v ≠ 0`, the incidence map is onto
  (`TauCeti.markedLineIncidence_surjective`), and it induces a linear isomorphism from the
  quotient of `Hom(K², V)` by the line of the marked line onto `K × V/Kv × V/Kw`
  (`TauCeti.markedLineIncidenceEquiv`). Since the conditions are linear, the incidence map is its
  own linearization. The quotient by the line of `A` is identified with the tangent space of
  `ℙ(Hom(K², V))` at `[A]`, and the target with the normal space of `H × {p} × {q}` in `ℙ(V)³` at
  the image point: `V/ker φ ≅ K` along `H`, and the full tangent spaces `V/Kv` and `V/Kw` at the
  two fixed points. In this sense the evaluation map of the three-pointed lines is transverse to
  `H × {p} × {q}`. With `V = ℂⁿ⁺¹` both sides have complex dimension `2n + 1`, and the isomorphism
  is complex linear, which is why the intersection point counts with sign `+1` for the complex
  orientations; that orientation comparison is not formalized here.
* **The projective statement.** For points `p ≠ q` of `ℙ(V)` off `H`, exactly one map
  `ℙ(K²) → ℙ(V)` induced by an injective linear map sends `[0 : 1]` into `H`, `[1 : 1]` to `p` and
  `[1 : 0]` to `q` (`TauCeti.existsUnique_markedLine`). An injective linear map satisfies the
  incidence conditions for the representatives of `p` and `q` exactly when the map it induces
  satisfies these projective conditions (`TauCeti.mem_ker_markedLineIncidence_iff_map`). Two
  injective linear maps satisfying the conditions differ by a nonzero scalar, which does not
  change the induced map (`Projectivization.map_smul_eq_map`).

The hypotheses cannot be dropped, except for one case over the field with two elements. If `p`
lies on `H` but `q` does not, `φ` vanishes at the marked points `0` and `1`, hence at the
difference `A [1 : 0]` of their representatives, which lies on the line `K w` with `φ w ≠ 0`; so
`A [1 : 0] = 0` and no marked line exists
(`TauCeti.not_exists_markedLine_of_mem_projectivization`). If `q` lies on `H` but `p` does not, the
line through `p` and `q` meets `H` only at `q`, so the marked points `0` and `∞` would both be sent
to `q`, which an injective `A` cannot do. If `p` and `q` both lie on `H`, so does the whole line
through them, and each of its points other than `p` and `q` can be the marked point `0`. When `K`
has more than two elements there are at least two such points, so uniqueness fails; over the field
with two elements the line has exactly three points, and the marked line is still unique. If
`p = q`, an injective `A` cannot send the distinct points `[1 : 1]` and `[1 : 0]` to the same
point.

## Main definitions

* `TauCeti.markedLine`: the homogeneous coordinates of the line through `[v]` and `[w]` marked at
  its point on `ker φ`.
* `TauCeti.markedLineIncidence`: the linear incidence conditions of a marked line.
* `TauCeti.markedLineIncidenceEquiv`: the incidence isomorphism from the quotient by the line of
  the marked line.

## Main results

* `TauCeti.ker_markedLineIncidence`, `TauCeti.markedLineIncidence_surjective`: the solutions of
  the incidence conditions are the multiples of the marked line, and the conditions are
  independent.
* `TauCeti.markedLine_injective`: the marked line is a line.
* `TauCeti.existsUnique_markedLine`: there is exactly one line through `p` and `q` marked at its
  point on `H`.
* `TauCeti.not_exists_markedLine_of_mem_projectivization`: there is none when `p` lies on `H` and
  `q` does not.

## References

* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*,
  arXiv:alg-geom/9608011, §10, for the count of lines through two points meeting a hyperplane in
  the quantum cohomology of `ℙⁿ`.
-/

public section

namespace TauCeti

open Function Module Projectivization Submodule
open scoped LinearAlgebra.Projectivization

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-! ### The marked line -/

/-- **The line through `[v]` and `[w]` marked at its point on `ker φ`**, in homogeneous
coordinates: the linear map `K² → V` sending `(x₀, x₁)` to `x₀ φ(v) w + x₁ (φ(w) v - φ(v) w)`.
It sends `[1 : 0]` to `φ(v) w`, `[1 : 1]` to `φ(w) v` and `[0 : 1]` into `ker φ`; so when
`φ v ≠ 0` and `φ w ≠ 0` it sends `[1 : 0]` to `[w]` and `[1 : 1]` to `[v]`. -/
noncomputable def markedLine (φ : Dual K V) (v w : V) : (Fin 2 → K) →ₗ[K] V :=
  Fintype.linearCombination K ![φ v • w, φ w • v - φ v • w]

variable {φ : Dual K V} {v w : V}

/-- The marked line sends `(x₀, x₁)` to `x₀ φ(v) w + x₁ (φ(w) v - φ(v) w)`. -/
theorem markedLine_apply (x : Fin 2 → K) :
    markedLine φ v w x = x 0 • φ v • w + x 1 • (φ w • v - φ v • w) := by
  simp [markedLine, Fintype.linearCombination_apply, Fin.sum_univ_two]

/-- The marked line sends `[1 : 0]`, the marked point `∞`, to `φ(v) w`. -/
@[simp]
theorem markedLine_single_zero_one : markedLine φ v w (Pi.single 0 1) = φ v • w := by
  simp [markedLine]

/-- The marked line sends `[0 : 1]`, the marked point `0`, to `φ(w) v - φ(v) w`. -/
@[simp]
theorem markedLine_single_one_one : markedLine φ v w (Pi.single 1 1) = φ w • v - φ v • w := by
  simp [markedLine]

/-- The marked line sends `[1 : 1]`, the marked point `1`, to `φ(w) v`. -/
@[simp]
theorem markedLine_one : markedLine φ v w 1 = φ w • v := by
  simp [markedLine_apply]

/-- The marked point `0` of the marked line lies on the hyperplane `ker φ`. -/
theorem apply_markedLine_single_one_one_eq_zero : φ (markedLine φ v w (Pi.single 1 1)) = 0 := by
  simp [mul_comm]

/-- **The marked line is a line.** When `v` and `w` are linearly independent and neither lies in
`ker φ`, the marked line `K² → V` is injective. -/
theorem markedLine_injective (hvw : LinearIndependent K ![v, w]) (hv : φ v ≠ 0) (hw : φ w ≠ 0) :
    Injective (markedLine φ v w) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  -- In the basis `v, w` the image of `x` has the coordinates `x₁ φ(w)` and `(x₀ - x₁) φ(v)`.
  have h : (x 1 * φ w) • v + ((x 0 - x 1) * φ v) • w = 0 := by
    rw [← hx, markedLine_apply]
    module
  obtain ⟨h₁, h₀⟩ := LinearIndependent.pair_iff.1 hvw _ _ h
  have hx₁ : x 1 = 0 := (mul_eq_zero.1 h₁).resolve_right hw
  have hx₀ : x 0 = 0 := by
    simpa [hx₁] using (mul_eq_zero.1 h₀).resolve_right hv
  ext i
  fin_cases i <;> simp [hx₀, hx₁]

/-! ### The incidence conditions -/

/-- **The incidence conditions of a marked line.** For homogeneous coordinates `A : K² → V` of a
marked line, the triple `(φ (A [0 : 1]), A [1 : 1] mod K v, A [1 : 0] mod K w)`. It vanishes
exactly when the marked point `0` lies on `ker φ`, the marked point `1` on the line `K v` and the
marked point `∞` on the line `K w`. -/
noncomputable def markedLineIncidence (φ : Dual K V) (v w : V) :
    ((Fin 2 → K) →ₗ[K] V) →ₗ[K] K × (V ⧸ K ∙ v) × (V ⧸ K ∙ w) :=
  (φ ∘ₗ LinearMap.applyₗ (Pi.single 1 1)).prod
    (((K ∙ v).mkQ ∘ₗ LinearMap.applyₗ 1).prod ((K ∙ w).mkQ ∘ₗ LinearMap.applyₗ (Pi.single 0 1)))

@[simp]
theorem markedLineIncidence_apply (A : (Fin 2 → K) →ₗ[K] V) :
    markedLineIncidence φ v w A =
      (φ (A (Pi.single 1 1)), (K ∙ v).mkQ (A 1), (K ∙ w).mkQ (A (Pi.single 0 1))) :=
  (rfl)

/-- The homogeneous coordinates `A` of a marked line satisfy the incidence conditions exactly when
`φ (A [0 : 1]) = 0`, `A [1 : 1] ∈ K v` and `A [1 : 0] ∈ K w`. -/
theorem mem_ker_markedLineIncidence_iff {A : (Fin 2 → K) →ₗ[K] V} :
    A ∈ LinearMap.ker (markedLineIncidence φ v w) ↔
      φ (A (Pi.single 1 1)) = 0 ∧ A 1 ∈ K ∙ v ∧ A (Pi.single 0 1) ∈ K ∙ w := by
  simp only [LinearMap.mem_ker, markedLineIncidence_apply, Prod.mk_eq_zero, mkQ_apply,
    Submodule.Quotient.mk_eq_zero]

/-- The marked line satisfies its incidence conditions. -/
theorem markedLineIncidence_markedLine : markedLineIncidence φ v w (markedLine φ v w) = 0 :=
  mem_ker_markedLineIncidence_iff.2
    ⟨apply_markedLine_single_one_one_eq_zero, by simp [mem_span_singleton],
      by simp [mem_span_singleton]⟩

/-- **The solutions of the incidence conditions.** When `[v]` lies off `ker φ`, the homogeneous
coordinates satisfying the incidence conditions are exactly the multiples of the marked line. -/
theorem ker_markedLineIncidence (hv : φ v ≠ 0) :
    LinearMap.ker (markedLineIncidence φ v w) = K ∙ markedLine φ v w := by
  refine le_antisymm (fun A hA ↦ ?_)
    ((span_singleton_le_iff_mem _ _).2 markedLineIncidence_markedLine)
  obtain ⟨hφ, ha, hb⟩ := mem_ker_markedLineIncidence_iff.1 hA
  obtain ⟨a, ha⟩ := mem_span_singleton.1 ha
  obtain ⟨b, hb⟩ := mem_span_singleton.1 hb
  -- The marked point `0` is `A [1 : 1] - A [1 : 0] = a v - b w`, and it lies on `ker φ`.
  have h₁ : A (Pi.single 1 1) = a • v - b • w := by rw [A.map_single_one_one_eq_sub, ha, hb]
  have hab : a * φ v = b * φ w := by simpa [h₁, sub_eq_zero] using hφ
  -- Solving `hab` for `a`, the marked point `0` is `(b / φ v) (φ w v - φ v w)`.
  have ha' : a = b / φ v * φ w := by rw [div_mul_eq_mul_div, eq_div_iff hv]; exact hab
  refine mem_span_singleton.2 ⟨b / φ v, ?_⟩
  refine (Pi.basisFun K (Fin 2)).ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · simp [← hb, smul_smul, div_mul_cancel₀ _ hv]
  · simp only [Pi.basisFun_apply, LinearMap.smul_apply, markedLine_single_one_one, h₁, ha']
    match_scalars <;> field_simp

/-- **Every nonzero solution of the incidence conditions is a line.** When `v` and `w` are
linearly independent and off `ker φ`, a nonzero `A` satisfying the incidence conditions is
injective. -/
theorem injective_of_mem_ker_markedLineIncidence (hvw : LinearIndependent K ![v, w])
    (hv : φ v ≠ 0) (hw : φ w ≠ 0) {A : (Fin 2 → K) →ₗ[K] V}
    (hA : A ∈ LinearMap.ker (markedLineIncidence φ v w)) (hA₀ : A ≠ 0) : Injective A := by
  rw [ker_markedLineIncidence hv] at hA
  obtain ⟨c, rfl⟩ := mem_span_singleton.1 hA
  have hc : c ≠ 0 := by rintro rfl; simp at hA₀
  exact (smul_right_injective V hc).comp (markedLine_injective hvw hv hw)

/-- **The incidence conditions are independent.** When `[v]` lies off `ker φ`, the incidence map
is onto: every value of `φ` at the marked point `0` and every position of the marked points `1`
and `∞` modulo the lines `K v` and `K w` is attained. -/
theorem markedLineIncidence_surjective (hv : φ v ≠ 0) :
    Surjective (markedLineIncidence φ v w) := by
  rintro ⟨c, x, y⟩
  obtain ⟨x, rfl⟩ := (K ∙ v).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (K ∙ w).mkQ_surjective y
  -- Send `[1 : 0]` to `y` and `[0 : 1]` to `x - y + t v`, with `t` adjusting the value of `φ`.
  set t := (c - φ (x - y)) / φ v
  refine ⟨Fintype.linearCombination K ![y, x - y + t • v], ?_⟩
  have h₁ : Fintype.linearCombination K ![y, x - y + t • v] 1 = x + t • v := by
    simp [Fintype.linearCombination_apply, Fin.sum_univ_two]
    abel
  rw [markedLineIncidence_apply, h₁]
  simp only [Fintype.linearCombination_apply_single, one_smul, Matrix.cons_val_zero,
    Matrix.cons_val_one, map_add, map_smul, smul_eq_mul, Prod.mk.injEq, and_true]
  refine ⟨?_, ?_⟩
  · rw [show t * φ v = c - φ (x - y) from div_mul_cancel₀ _ hv]
    ring
  · have hv₀ : (K ∙ v).mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).2 (mem_span_singleton_self v)
    rw [hv₀, smul_zero, add_zero]

/-- **The incidence isomorphism.** When `[v]` lies off `ker φ`, the incidence map induces a linear
isomorphism from the quotient of `Hom(K², V)` by the line of the marked line onto
`K × V/Kv × V/Kw`. -/
noncomputable def markedLineIncidenceEquiv (hv : φ v ≠ 0) :
    (((Fin 2 → K) →ₗ[K] V) ⧸ K ∙ markedLine φ v w) ≃ₗ[K] K × (V ⧸ K ∙ v) × (V ⧸ K ∙ w) :=
  (quotEquivOfEq _ _ (ker_markedLineIncidence hv).symm).trans
    ((markedLineIncidence φ v w).quotKerEquivOfSurjective (markedLineIncidence_surjective hv))

@[simp]
theorem markedLineIncidenceEquiv_mk (hv : φ v ≠ 0) (A : (Fin 2 → K) →ₗ[K] V) :
    markedLineIncidenceEquiv hv (Submodule.Quotient.mk A) = markedLineIncidence φ v w A := by
  simp [markedLineIncidenceEquiv, quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

/-! ### The marked line through two points of projective space -/

/-- **The incidence conditions in projective terms.** An injective linear map `A` satisfies the
incidence conditions for the representatives of `p` and `q` exactly when the map it induces sends
`[0 : 1]` into `ℙ(ker φ)`, `[1 : 1]` to `p` and `[1 : 0]` to `q`. -/
theorem mem_ker_markedLineIncidence_iff_map {p q : ℙ K V} {A : (Fin 2 → K) →ₗ[K] V}
    (hA : Injective A) :
    A ∈ LinearMap.ker (markedLineIncidence φ p.rep q.rep) ↔
      map A hA (mk K (Pi.single 1 1) (by simp)) ∈ (LinearMap.ker φ).projectivization ∧
        map A hA (mk K 1 one_ne_zero) = p ∧ map A hA (mk K (Pi.single 0 1) (by simp)) = q := by
  rw [mem_ker_markedLineIncidence_iff, map_mk, map_mk, map_mk, mk_mem_projectivization_iff,
    LinearMap.mem_ker]
  conv_rhs => rw [← mk_rep p, ← mk_rep q, mk_eq_mk_iff_mem_span, mk_eq_mk_iff_mem_span]

/-- **The line through two points, marked at its point on a hyperplane.** Let `p ≠ q` be points of
`ℙ(V)` off the hyperplane `ℙ(ker φ)`. Exactly one map `ℙ(K²) → ℙ(V)` induced by an injective
linear map sends the marked point `[0 : 1]` into the hyperplane, the marked point `[1 : 1]` to `p`
and the marked point `[1 : 0]` to `q`: the line through `p` and `q`, marked at its point on the
hyperplane. Over `ℂ` this says that exactly one three-pointed line of `ℂℙⁿ` with an irreducible
domain is sent to `H × {p} × {q}` by the evaluation map, the enumerative content of the three-point
invariant `⟨x, xⁿ, xⁿ⟩_L`; it does not treat stable maps or the invariant itself. -/
theorem existsUnique_markedLine {p q : ℙ K V} (hpq : p ≠ q)
    (hp : p ∉ (LinearMap.ker φ).projectivization) (hq : q ∉ (LinearMap.ker φ).projectivization) :
    ∃! u : ℙ K (Fin 2 → K) → ℙ K V,
      (∃ (A : (Fin 2 → K) →ₗ[K] V) (hA : Injective A), map A hA = u) ∧
        u (mk K (Pi.single 1 1) (by simp)) ∈ (LinearMap.ker φ).projectivization ∧
        u (mk K 1 one_ne_zero) = p ∧ u (mk K (Pi.single 0 1) (by simp)) = q := by
  rw [mem_projectivization_iff_rep_mem, LinearMap.mem_ker] at hp hq
  have hpq' : LinearIndependent K ![p.rep, q.rep] := by
    rw [← independent_mk_iff_LinearIndependent p.rep_ne_zero q.rep_ne_zero, mk_rep, mk_rep]
    exact (independent_pair_iff_ne p q).2 hpq
  have hM := markedLine_injective hpq' hp hq
  refine ⟨map _ hM, ⟨⟨_, hM, rfl⟩, (mem_ker_markedLineIncidence_iff_map hM).1
    (LinearMap.mem_ker.2 markedLineIncidence_markedLine)⟩, ?_⟩
  · rintro u ⟨⟨A, hA, rfl⟩, h₀, h₁, h₂⟩
    -- `A` solves the incidence conditions, so it is a nonzero multiple of the marked line.
    have hker := (mem_ker_markedLineIncidence_iff_map hA).2 ⟨h₀, h₁, h₂⟩
    rw [ker_markedLineIncidence hp] at hker
    obtain ⟨c, rfl⟩ := mem_span_singleton.1 hker
    exact map_smul_eq_map hM hA

/-- **No marked line through a point of the hyperplane.** If `p` lies on the hyperplane
`ℙ(ker φ)` and `q` does not, no map `ℙ(K²) → ℙ(V)` induced by an injective linear map sends
`[0 : 1]` into the hyperplane, `[1 : 1]` to `p` and `[1 : 0]` to `q`. -/
theorem not_exists_markedLine_of_mem_projectivization {p q : ℙ K V}
    (hp : p ∈ (LinearMap.ker φ).projectivization) (hq : q ∉ (LinearMap.ker φ).projectivization) :
    ¬∃ (A : (Fin 2 → K) →ₗ[K] V) (hA : Injective A),
      map A hA (mk K (Pi.single 1 1) (by simp)) ∈ (LinearMap.ker φ).projectivization ∧
        map A hA (mk K 1 one_ne_zero) = p ∧ map A hA (mk K (Pi.single 0 1) (by simp)) = q := by
  rintro ⟨A, hA, h₀, h₁, h₂⟩
  rw [mem_projectivization_iff_rep_mem, LinearMap.mem_ker] at hp hq
  obtain ⟨hφ, ha, hb⟩ :=
    mem_ker_markedLineIncidence_iff.1 ((mem_ker_markedLineIncidence_iff_map hA).2 ⟨h₀, h₁, h₂⟩)
  obtain ⟨a, ha⟩ := mem_span_singleton.1 ha
  obtain ⟨b, hb⟩ := mem_span_singleton.1 hb
  -- `φ` vanishes at `A [1 : 0] = A [1 : 1] - A [0 : 1] = b q.rep`, so `b = 0`.
  have hφb : b * φ q.rep = 0 := by
    simpa [A.map_single_one_one_eq_sub, ← ha, ← hb, hp] using hφ
  have hb₀ : b = 0 := (mul_eq_zero.1 hφb).resolve_right hq
  have : A (Pi.single 0 1) = 0 := by rw [← hb, hb₀, zero_smul]
  exact (Pi.single_ne_zero_iff.2 one_ne_zero) (hA (this.trans (map_zero A).symm))

end TauCeti
