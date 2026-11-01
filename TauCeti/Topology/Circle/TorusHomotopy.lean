/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Homotopy.Lifting
public import TauCeti.Topology.Circle.MatrixAction

/-!
# Homotopy classes of self-maps of the torus

Every continuous self-map of the torus `S¹ × S¹` is homotopic to exactly one monomial map
`Matrix.torusMap M`, `(a, b) ↦ (a ^ M₀₀ * b ^ M₀₁, a ^ M₁₀ * b ^ M₁₁)`, for an integral
`2 × 2` matrix `M`. So the homotopy classes of self-maps of the torus are the integral matrices,
composition corresponding to the product of matrices, and the self-homeomorphisms of the torus are
homotopic to the linear homeomorphisms `Matrix.GeneralLinearGroup.torusHomeomorph A`,
`A ∈ GL₂(ℤ)`. This is the case of the torus, a `K(ℤ², 1)`, of the classification of maps into an
Eilenberg–MacLane space by their action on the fundamental group.

The proof lifts along the universal covering `ℝ × ℝ → S¹ × S¹`, `(x, y) ↦ (exp (i x), exp (i y))`.
A coordinate `g` of a self-map of the torus, read on `ℝ × ℝ`, lifts through `exp : ℝ → S¹` to a
continuous `G : ℝ × ℝ → ℝ`, since `ℝ × ℝ` is simply connected. Translating by a period `2π` in
either variable changes `G` by an integer multiple of `2π`, which is constant because `ℝ × ℝ` is
connected; call these integers `m` and `n`. Then `G` differs from the linear map
`(x, y) ↦ m x + n y` by a function periodic in both variables, and the straight-line homotopy
between them descends to the torus, from `g` to the monomial `(a, b) ↦ a ^ m * b ^ n`. The
integers are determined by the homotopy class: lifting a homotopy between two monomials to
`[0, 1] × ℝ × ℝ`, the change under translation by a period is again constant, and it computes the
exponents at both ends.

The matrix of a self-map `f` is `ContinuousMap.torusMatrix f`. Two self-maps are homotopic
exactly when their matrices agree (`ContinuousMap.homotopic_iff_torusMatrix_eq`), the matrix of a
composite is the product of the matrices (`ContinuousMap.torusMatrix_comp`), and the matrix of a
homeomorphism is invertible (`Homeomorph.isUnit_torusMatrix`). The homotopy class of a gluing of
two solid tori along their boundary tori is therefore an element of `GL₂(ℤ)`; that homotopic
homeomorphisms of the torus are isotopic, which upgrades this to the isotopy classification used
for Dehn filling, is not proved here.

## Main definitions

* `ContinuousMap.torusMatrix f`: the integral matrix of the monomial map homotopic to a self-map
  `f` of the torus.

## Main results

* `ContinuousMap.homotopic_torusContinuousMap_torusMatrix`: every self-map of the torus is
  homotopic to the monomial map of its matrix.
* `Matrix.torusContinuousMap_homotopic_iff`: two monomial maps are homotopic exactly when their
  matrices are equal.
* `ContinuousMap.homotopic_iff_torusMatrix_eq`: two self-maps of the torus are homotopic exactly
  when their matrices are equal.
* `ContinuousMap.torusMatrix_comp`, `ContinuousMap.torusMatrix_id`: the matrix is multiplicative.
* `Homeomorph.isUnit_torusMatrix`: the matrix of a self-homeomorphism of the torus is invertible.
* `Homeomorph.existsUnique_homotopic_torusHomeomorph`: every self-homeomorphism of the torus is
  homotopic to the linear homeomorphism of exactly one matrix in `GL₂(ℤ)`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Proposition 1.30 (homotopy
  lifting for covering spaces) and Proposition 1B.9 (maps into a `K(G, 1)` are classified up to
  homotopy by the homomorphisms they induce on fundamental groups).
* B. Farb, D. Margalit, *A Primer on Mapping Class Groups*, Princeton University Press (2012),
  Section 2.2 (the mapping class group of the torus, through the action of homeomorphisms on the
  fundamental group).
-/

public section

noncomputable section

open Real Function

namespace TauCeti.TorusHomotopy

/-! ### Lifting maps along the covering `ℝ × ℝ → S¹ × S¹` -/

/-- The universal covering `ℝ × ℝ → S¹ × S¹`, `(x, y) ↦ (exp (i x), exp (i y))`. -/
private def cover (v : ℝ × ℝ) : Circle × Circle :=
  (Circle.exp v.1, Circle.exp v.2)

@[simp]
private theorem cover_apply (v : ℝ × ℝ) : cover v = (Circle.exp v.1, Circle.exp v.2) :=
  (rfl)

private theorem isOpenQuotientMap_cover : IsOpenQuotientMap cover := by
  have h : IsOpenQuotientMap Circle.exp :=
    ⟨Circle.exp_surjective, Circle.exp.continuous, Circle.isCoveringMap_exp.isOpenMap⟩
  exact h.prodMap h

/-- Two points of `ℝ × ℝ` lie over the same point of the torus exactly when they differ by integer
multiples of `2π` in both coordinates. -/
private theorem cover_eq_cover_iff {v w : ℝ × ℝ} :
    cover v = cover w ↔ ∃ a b : ℤ, v = w + (a * (2 * π), b * (2 * π)) := by
  simp only [cover_apply, Circle.exp_eq_exp, Prod.ext_iff, Prod.fst_add,
    Prod.snd_add]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨a, b, ha, hb⟩
  · rintro ⟨a, b, ha, hb⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩

/-- On a preconnected space, two continuous real functions with the same exponential differ by a
constant. -/
private theorem exists_eq_add_of_exp_eq {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    [Nonempty A] {G G' : A → ℝ} (hG : Continuous G) (hG' : Continuous G')
    (h : ∀ a, Circle.exp (G a) = Circle.exp (G' a)) : ∃ c : ℝ, ∀ a, G a = G' a + c := by
  obtain ⟨a₀⟩ := ‹Nonempty A›
  refine ⟨G a₀ - G' a₀, fun a ↦ ?_⟩
  have := Circle.isCoveringMap_exp.const_of_comp (g := fun a ↦ G a - G' a) (hG.sub hG')
    (fun a a' ↦ by simp [Circle.exp_sub, h]) a a₀
  linarith

/-- On a preconnected space, a continuous real function whose exponential is invariant under a
continuous self-map `τ` changes under `τ` by a constant integer multiple of `2π`. -/
private theorem exists_int_forall_eq_add {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    [Nonempty A] {G : A → ℝ} (hG : Continuous G) {τ : A → A} (hτ : Continuous τ)
    (h : ∀ a, Circle.exp (G (τ a)) = Circle.exp (G a)) :
    ∃ m : ℤ, ∀ a, G (τ a) = G a + m * (2 * π) := by
  obtain ⟨c, hc⟩ := exists_eq_add_of_exp_eq (hG.comp hτ) hG h
  replace hc : ∀ a, G (τ a) = G a + c := hc
  obtain ⟨a₀⟩ := ‹Nonempty A›
  have hexp : Circle.exp c = 1 := by
    have := h a₀
    rwa [hc a₀, Circle.exp_add, mul_eq_left] at this
  obtain ⟨m, hm⟩ := Circle.exp_eq_one.1 hexp
  exact ⟨m, fun a ↦ by rw [hc a, hm]⟩

/-- The monomial `(a, b) ↦ a ^ m * b ^ n` from the torus to the circle. -/
private def monomial (m n : ℤ) : C(Circle × Circle, Circle) :=
  ⟨fun q ↦ q.1 ^ m * q.2 ^ n, by fun_prop⟩

@[simp]
private theorem monomial_apply (m n : ℤ) (q : Circle × Circle) :
    monomial m n q = q.1 ^ m * q.2 ^ n :=
  (rfl)

/-- Read on `ℝ × ℝ`, the monomial `(a, b) ↦ a ^ m * b ^ n` is the exponential of the linear map
`(x, y) ↦ m x + n y`. -/
private theorem monomial_cover (m n : ℤ) (v : ℝ × ℝ) :
    monomial m n (cover v) = Circle.exp (m * v.1 + n * v.2) := by
  simp [Circle.exp_add]

/-- A lift through `exp` of a monomial read on `ℝ × ℝ` changes by `2π m` under translation by
`(2π, 0)` and by `2π n` under translation by `(0, 2π)`. -/
private theorem lift_add_of_monomial {m n : ℤ} {G : ℝ × ℝ → ℝ} (hG : Continuous G)
    (h : ∀ v, Circle.exp (G v) = monomial m n (cover v)) (v : ℝ × ℝ) :
    G (v + (2 * π, 0)) = G v + m * (2 * π) ∧ G (v + (0, 2 * π)) = G v + n * (2 * π) := by
  obtain ⟨c, hc⟩ := exists_eq_add_of_exp_eq (G' := fun v : ℝ × ℝ ↦ m * v.1 + n * v.2) hG
    (by fun_prop) fun v ↦ by rw [h, monomial_cover]
  constructor <;>
  · simp only [hc, Prod.fst_add, Prod.snd_add]
    ring

/-! ### Every coordinate is homotopic to a monomial -/

/-- The covering `ℝ × ℝ → S¹ × S¹` with a parameter in `[0, 1]`, along which homotopies are read. -/
private def intervalCover : C(unitInterval × (ℝ × ℝ), unitInterval × (Circle × Circle)) :=
  ⟨Prod.map id cover, by unfold cover; fun_prop⟩

@[simp]
private theorem intervalCover_apply (p : unitInterval × (ℝ × ℝ)) :
    intervalCover p = (p.1, cover p.2) :=
  (rfl)

/-- **The straight-line homotopy descends to the torus.** Let `G : ℝ × ℝ → ℝ` lift a map
`g : S¹ × S¹ → S¹` through `exp`, and change by `2π m` and `2π n` under the two periods. Then
`G` minus the linear map `(x, y) ↦ m x + n y` is periodic, so the straight-line homotopy from `G`
to that linear map, exponentiated, descends to a homotopy from `g` to the monomial
`(a, b) ↦ a ^ m * b ^ n`. -/
private theorem homotopic_monomial_of_lift {g : C(Circle × Circle, Circle)} {G : ℝ × ℝ → ℝ}
    (hG : Continuous G) (hGg : ∀ v, Circle.exp (G v) = g (cover v)) {m n : ℤ}
    (hm : ∀ v, G (v + (2 * π, 0)) = G v + m * (2 * π))
    (hn : ∀ v, G (v + (0, 2 * π)) = G v + n * (2 * π)) :
    g.Homotopic (monomial m n) := by
  let ℓ : ℝ × ℝ → ℝ := fun v ↦ m * v.1 + n * v.2
  let ψ : ℝ × ℝ → ℝ := fun v ↦ G v - ℓ v
  have hψ₁ : Periodic ψ (2 * π, 0) := fun v ↦ by
    simp only [ψ, ℓ, hm, Prod.fst_add, Prod.snd_add]
    ring
  have hψ₂ : Periodic ψ (0, 2 * π) := fun v ↦ by
    simp only [ψ, ℓ, hn, Prod.fst_add, Prod.snd_add]
    ring
  let Φ : C(unitInterval × (ℝ × ℝ), Circle) :=
    ⟨fun p ↦ Circle.exp (ℓ p.2 + (1 - (p.1 : ℝ)) * ψ p.2), by
      simp only [ψ, ℓ]
      fun_prop⟩
  have hq : Topology.IsQuotientMap intervalCover :=
    (IsOpenQuotientMap.id.prodMap isOpenQuotientMap_cover).isQuotientMap
  -- `Φ` only depends on the image in `[0, 1] × (S¹ × S¹)`.
  have hΦ : FactorsThrough Φ intervalCover := by
    rintro ⟨s, v⟩ ⟨t, w⟩ h
    simp only [intervalCover_apply, Prod.mk.injEq] at h
    obtain ⟨rfl, hvw⟩ := h
    obtain ⟨a, b, rfl⟩ := cover_eq_cover_iff.1 hvw
    have hsplit : ((a : ℝ) * (2 * π), (b : ℝ) * (2 * π)) =
        a • ((2 * π, 0) : ℝ × ℝ) + b • ((0, 2 * π) : ℝ × ℝ) := by
      ext <;> simp
    have hper : ψ (w + (a * (2 * π), b * (2 * π))) = ψ w := by
      rw [hsplit]
      exact ((hψ₁.zsmul a).add_period (hψ₂.zsmul b)) w
    simp only [Φ, ContinuousMap.coe_mk, hper]
    rw [Circle.exp_eq_exp]
    exact ⟨m * a + n * b, by simp only [ℓ, Prod.fst_add, Prod.snd_add]; push_cast; ring⟩
  let F := hq.lift Φ hΦ
  have hF (t : unitInterval) (v : ℝ × ℝ) : F (t, cover v) = Φ (t, v) :=
    DFunLike.congr_fun (hq.lift_comp Φ hΦ) (t, v)
  refine ⟨⟨F, fun q ↦ ?_, fun q ↦ ?_⟩⟩
  · obtain ⟨v, rfl⟩ := isOpenQuotientMap_cover.surjective q
    simp only [ContinuousMap.toFun_eq_coe, hF, Φ, ContinuousMap.coe_mk, Set.Icc.coe_zero,
      sub_zero, one_mul, ψ, add_sub_cancel, hGg]
  · obtain ⟨v, rfl⟩ := isOpenQuotientMap_cover.surjective q
    simp only [ContinuousMap.toFun_eq_coe, hF, Φ, ContinuousMap.coe_mk, Set.Icc.coe_one,
      sub_self, zero_mul, add_zero, ℓ, monomial_cover]

/-- **A map from the torus to the circle is homotopic to a monomial.** -/
private theorem exists_homotopic_monomial (g : C(Circle × Circle, Circle)) :
    ∃ m n : ℤ, g.Homotopic (monomial m n) := by
  -- Lift `g`, read on the simply connected space `ℝ × ℝ`, through `exp`.
  let gc : C(ℝ × ℝ, Circle) := g.comp ⟨cover, by unfold cover; fun_prop⟩
  obtain ⟨e₀, he₀⟩ := Circle.exp_surjective (gc 0)
  obtain ⟨G, -, hG⟩ :=
    (Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts gc 0 e₀ he₀).exists
  have hG' (v : ℝ × ℝ) : Circle.exp (G v) = g (cover v) := congrFun hG v
  have hper (c : ℝ × ℝ) (hc : cover c = 1) (v : ℝ × ℝ) :
      Circle.exp (G (v + c)) = Circle.exp (G v) := by
    rw [hG', hG', show cover (v + c) = cover v * cover c by simp [Circle.exp_add], hc, mul_one]
  -- Translating by a period changes the lift by an integer multiple of `2π`.
  obtain ⟨m, hm⟩ := exists_int_forall_eq_add G.continuous (τ := fun v ↦ v + (2 * π, 0))
    (by fun_prop) (hper _ (by simp))
  obtain ⟨n, hn⟩ := exists_int_forall_eq_add G.continuous (τ := fun v ↦ v + (0, 2 * π))
    (by fun_prop) (hper _ (by simp))
  exact ⟨m, n, homotopic_monomial_of_lift G.continuous hG' hm hn⟩

/-- **Homotopic monomials have the same exponents.** -/
private theorem eq_of_homotopic_monomial {m n m' n' : ℤ}
    (h : (monomial m n).Homotopic (monomial m' n')) :
    m = m' ∧ n = n' := by
  obtain ⟨K⟩ := h
  -- Lift the homotopy, read on `[0, 1] × ℝ × ℝ`, starting from the linear lift of the monomial.
  let Kc : C(unitInterval × (ℝ × ℝ), Circle) := K.toContinuousMap.comp intervalCover
  let ℓ : C(ℝ × ℝ, ℝ) := ⟨fun v ↦ m * v.1 + n * v.2, by fun_prop⟩
  have h0 (v : ℝ × ℝ) : Kc (0, v) = Circle.exp (ℓ v) := by
    simp only [Kc, ContinuousMap.comp_apply, intervalCover_apply,
      ContinuousMap.Homotopy.coe_toContinuousMap, K.apply_zero, monomial_cover, ℓ,
      ContinuousMap.coe_mk]
  let L := Circle.isCoveringMap_exp.liftHomotopy Kc ℓ h0
  have hL (p : unitInterval × (ℝ × ℝ)) : Circle.exp (L p) = Kc p :=
    congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts Kc ℓ h0) p
  have hL0 (v : ℝ × ℝ) : L (0, v) = ℓ v := Circle.isCoveringMap_exp.liftHomotopy_zero Kc ℓ h0 v
  have hL1 (v : ℝ × ℝ) : Circle.exp (L (1, v)) = monomial m' n' (cover v) := by
    rw [hL]
    simp only [Kc, ContinuousMap.comp_apply, intervalCover_apply,
      ContinuousMap.Homotopy.coe_toContinuousMap, K.apply_one]
  have hKc (c : ℝ × ℝ) (hc : cover c = 1) (p : unitInterval × (ℝ × ℝ)) :
      Circle.exp (L (p.1, p.2 + c)) = Circle.exp (L p) := by
    rw [hL, hL]
    simp only [Kc, ContinuousMap.comp_apply, intervalCover_apply]
    congr 2
    have : cover (p.2 + c) = cover p.2 * cover c := by simp [Circle.exp_add]
    rw [this, hc, mul_one]
  -- The change of the lift under translation by a period is constant on `[0, 1] × ℝ × ℝ`.
  have key (c : ℝ × ℝ) (hc : cover c = 1) : L (1, c) - L (1, 0) = ℓ c - ℓ 0 := by
    obtain ⟨k, hk⟩ := exists_int_forall_eq_add L.continuous
      (τ := fun p : unitInterval × (ℝ × ℝ) ↦ (p.1, p.2 + c)) (by fun_prop) (hKc c hc)
    have h₁ := hk (1, 0)
    have h₀ := hk (0, 0)
    simp only [zero_add] at h₁ h₀
    rw [hL0, hL0] at h₀
    linarith
  -- At the end of the homotopy, the lift is a lift of the second monomial.
  obtain ⟨hm, hn⟩ := lift_add_of_monomial (L.continuous.comp (by fun_prop :
    Continuous fun v : ℝ × ℝ ↦ ((1 : unitInterval), v))) hL1 0
  have k₁ := key (2 * π, 0) (by simp)
  have k₂ := key (0, 2 * π) (by simp)
  simp only [Function.comp_apply, zero_add] at hm hn
  simp only [ℓ, ContinuousMap.coe_mk, Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero,
    zero_add, sub_zero] at k₁ k₂
  have hπ : (2 * π) ≠ 0 := by positivity
  constructor
  · have : (m' : ℝ) * (2 * π) = m * (2 * π) := by linarith
    exact_mod_cast (mul_right_cancel₀ hπ this).symm
  · have : (n' : ℝ) * (2 * π) = n * (2 * π) := by linarith
    exact_mod_cast (mul_right_cancel₀ hπ this).symm

/-- The two coordinates of the monomial self-map of a matrix are the monomials of its rows. -/
private theorem prodMk_monomial (M : Matrix (Fin 2) (Fin 2) ℤ) :
    (monomial (M 0 0) (M 0 1)).prodMk (monomial (M 1 0) (M 1 1)) = M.torusContinuousMap :=
  ContinuousMap.ext fun q ↦ by simp

end TauCeti.TorusHomotopy

open TauCeti.TorusHomotopy

/-! ### The matrix of a self-map of the torus -/

namespace Matrix

/-- **Two monomial self-maps of the torus are homotopic exactly when their matrices are
equal.** -/
theorem torusContinuousMap_homotopic_iff {M N : Matrix (Fin 2) (Fin 2) ℤ} :
    M.torusContinuousMap.Homotopic N.torusContinuousMap ↔ M = N := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ .refl _⟩
  have hfst :=
    (ContinuousMap.Homotopic.refl (ContinuousMap.fst : C(Circle × Circle, Circle))).comp h
  have hsnd :=
    (ContinuousMap.Homotopic.refl (ContinuousMap.snd : C(Circle × Circle, Circle))).comp h
  have e₁ (M : Matrix (Fin 2) (Fin 2) ℤ) :
      (ContinuousMap.fst : C(Circle × Circle, Circle)).comp M.torusContinuousMap =
        monomial (M 0 0) (M 0 1) :=
    ContinuousMap.ext fun q ↦ by simp
  have e₂ (M : Matrix (Fin 2) (Fin 2) ℤ) :
      (ContinuousMap.snd : C(Circle × Circle, Circle)).comp M.torusContinuousMap =
        monomial (M 1 0) (M 1 1) :=
    ContinuousMap.ext fun q ↦ by simp
  rw [e₁, e₁] at hfst
  rw [e₂, e₂] at hsnd
  obtain ⟨h00, h01⟩ := eq_of_homotopic_monomial hfst
  obtain ⟨h10, h11⟩ := eq_of_homotopic_monomial hsnd
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

end Matrix

namespace ContinuousMap

/-- **Every self-map of the torus is homotopic to a monomial map.** -/
private theorem exists_homotopic_torusContinuousMap (f : C(Circle × Circle, Circle × Circle)) :
    ∃ M : Matrix (Fin 2) (Fin 2) ℤ, f.Homotopic M.torusContinuousMap := by
  obtain ⟨m₁, n₁, ⟨H₁⟩⟩ := exists_homotopic_monomial (ContinuousMap.fst.comp f)
  obtain ⟨m₂, n₂, ⟨H₂⟩⟩ := exists_homotopic_monomial (ContinuousMap.snd.comp f)
  refine ⟨!![m₁, n₁; m₂, n₂], ⟨(H₁.prodMk H₂).cast ?_ ?_⟩⟩
  · ext x <;> rfl
  · rw [← prodMk_monomial]
    simp

/-- The **matrix** of a self-map `f` of the torus: the integral matrix `M` whose monomial map
`(a, b) ↦ (a ^ M₀₀ * b ^ M₀₁, a ^ M₁₀ * b ^ M₁₁)` is homotopic to `f`
(`ContinuousMap.homotopic_torusContinuousMap_torusMatrix`). It is unique
(`ContinuousMap.torusMatrix_eq_iff`). -/
def torusMatrix (f : C(Circle × Circle, Circle × Circle)) : Matrix (Fin 2) (Fin 2) ℤ :=
  (exists_homotopic_torusContinuousMap f).choose

variable {f g : C(Circle × Circle, Circle × Circle)}

/-- A self-map of the torus is homotopic to the monomial map of its matrix. -/
theorem homotopic_torusContinuousMap_torusMatrix (f : C(Circle × Circle, Circle × Circle)) :
    f.Homotopic f.torusMatrix.torusContinuousMap :=
  (exists_homotopic_torusContinuousMap f).choose_spec

/-- The matrix of a self-map of the torus is the matrix of any monomial map homotopic to it. -/
theorem torusMatrix_eq_iff {M : Matrix (Fin 2) (Fin 2) ℤ} :
    f.torusMatrix = M ↔ f.Homotopic M.torusContinuousMap :=
  ⟨fun h ↦ h ▸ f.homotopic_torusContinuousMap_torusMatrix, fun h ↦
    Matrix.torusContinuousMap_homotopic_iff.1
      ((homotopic_torusContinuousMap_torusMatrix f).symm.trans h)⟩

/-- **The homotopy classification of self-maps of the torus.** Two self-maps of the torus are
homotopic exactly when their matrices are equal. -/
theorem homotopic_iff_torusMatrix_eq : f.Homotopic g ↔ f.torusMatrix = g.torusMatrix :=
  ⟨fun h ↦ torusMatrix_eq_iff.2 (h.trans g.homotopic_torusContinuousMap_torusMatrix),
    fun h ↦ (f.homotopic_torusContinuousMap_torusMatrix.trans
      (h ▸ (g.homotopic_torusContinuousMap_torusMatrix).symm))⟩

/-- The matrix of the monomial map of a matrix is that matrix. -/
@[simp]
theorem torusMatrix_torusContinuousMap (M : Matrix (Fin 2) (Fin 2) ℤ) :
    M.torusContinuousMap.torusMatrix = M :=
  torusMatrix_eq_iff.2 (.refl _)

/-- The matrix of the identity of the torus is the identity matrix. -/
@[simp]
theorem torusMatrix_id : (ContinuousMap.id (Circle × Circle)).torusMatrix = 1 := by
  rw [← Matrix.torusContinuousMap_one, torusMatrix_torusContinuousMap]

/-- The matrix of a composite of self-maps of the torus is the product of their matrices. -/
@[simp]
theorem torusMatrix_comp (f g : C(Circle × Circle, Circle × Circle)) :
    (f.comp g).torusMatrix = f.torusMatrix * g.torusMatrix := by
  rw [torusMatrix_eq_iff, ← Matrix.torusContinuousMap_comp]
  exact f.homotopic_torusContinuousMap_torusMatrix.comp g.homotopic_torusContinuousMap_torusMatrix

end ContinuousMap

namespace Homeomorph

/-- The matrix of a self-homeomorphism of the torus is invertible: its inverse is the matrix of the
inverse homeomorphism. -/
theorem isUnit_torusMatrix (h : Circle × Circle ≃ₜ Circle × Circle) :
    IsUnit (h : C(Circle × Circle, Circle × Circle)).torusMatrix := by
  refine ⟨⟨(h : C(Circle × Circle, Circle × Circle)).torusMatrix,
    (h.symm : C(Circle × Circle, Circle × Circle)).torusMatrix, ?_, ?_⟩, rfl⟩
  · rw [← ContinuousMap.torusMatrix_comp, Homeomorph.toContinuousMap_comp_symm,
      ContinuousMap.torusMatrix_id]
  · rw [← ContinuousMap.torusMatrix_comp, Homeomorph.symm_comp_toContinuousMap,
      ContinuousMap.torusMatrix_id]

/-- **Every self-homeomorphism of the torus is homotopic to a linear one**: it is homotopic to the
homeomorphism `Matrix.GeneralLinearGroup.torusHomeomorph A` of exactly one matrix `A ∈ GL₂(ℤ)`. -/
theorem existsUnique_homotopic_torusHomeomorph (h : Circle × Circle ≃ₜ Circle × Circle) :
    ∃! A : GL (Fin 2) ℤ, (h : C(Circle × Circle, Circle × Circle)).Homotopic
      (A.torusHomeomorph : C(Circle × Circle, Circle × Circle)) := by
  obtain ⟨A, hA⟩ := h.isUnit_torusMatrix
  refine ⟨A, ?_, fun B hB ↦ Units.ext ?_⟩
  · dsimp only
    rw [Matrix.GeneralLinearGroup.coe_continuousMap_torusHomeomorph, hA]
    exact (h : C(Circle × Circle, Circle × Circle)).homotopic_torusContinuousMap_torusMatrix
  · dsimp only at hB
    rw [Matrix.GeneralLinearGroup.coe_continuousMap_torusHomeomorph,
      ← ContinuousMap.torusMatrix_eq_iff] at hB
    rw [← hB, hA]

end Homeomorph
