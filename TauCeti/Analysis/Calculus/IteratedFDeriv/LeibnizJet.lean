/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Operator.Mul
import TauCeti.Analysis.Calculus.IteratedFDeriv.Mul
import TauCeti.Analysis.Normed.Module.Multilinear.Curry

/-!
# The Leibniz rule on jets of multilinear maps

Let `B : F →L G →L H` be a continuous bilinear map. A *jet* of order `n` with values in `F` is a
family `J = (J₀, …, Jₙ)` of continuous multilinear maps `Jᵢ : E [×i]→L F`, for instance the
iterated derivatives `Dⁱ f (x)` of a map `f : E → F` at a point. This file constructs the
continuous bilinear map `ContinuousLinearMap.leibnizJet B E n`, from the `F`-valued and the
`G`-valued jets of order `n` to `E [×n]→L H`, which computes the `n`-th derivative of
`y ↦ B (f y) (g y)` from the jets of `f` and `g`: for `C^n` maps `f` and `g`, and `m ≤ n`,

`Dᵐ (y ↦ B (f y) (g y)) (x) = leibnizJet B E m (D^• f (x)) (D^• g (x))`

(`ContinuousLinearMap.iteratedFDeriv_bilinear_eq_leibnizJet`). It is defined by the recursion
behind the Leibniz rule: `leibnizJet B E 0 J K = B J₀ K₀`, and `leibnizJet B E (n + 1) J K`,
curried on the left at `h`, is

`leibnizJet B E n (∂ₕ J) (init K) + leibnizJet B E n (init J) (∂ₕ K)`,

where `init` forgets the top entry of a jet (`TauCeti.jetInit`) and `∂ₕ` shifts it down by one,
`(∂ₕ J)ᵢ = Jᵢ₊₁ (h, ·)` (`TauCeti.jetShift`). Its norm is at most `2ⁿ ‖B‖`
(`ContinuousLinearMap.norm_leibnizJet_le`).

The point of having the derivative as a bilinear function of the jets, rather than only as an
iterated derivative, is that it applies to families of multilinear maps that are not known to be
derivatives of anything in some of the variables. If `f y = (fᵢ y)ᵢ` is a family of jets whose
entries of order at most `n` have derivative `D fᵢ (x) h = fᵢ₊₁ (x) (h, ·)` at `x`, and likewise
for `g`, then `y ↦ leibnizJet B E n (init (f y)) (init (g y))` has derivative
`leibnizJet B E (n + 1) (f x) (g x)` at `x`, curried on the left
(`ContinuousLinearMap.hasFDerivAt_leibnizJet`). Since `leibnizJet B E n` is bilinear and
continuous, derivatives in any other variable, such as time in a parabolic Hölder space, pass
through it by the product rule.

## Main declarations

* `TauCeti.jetInit`, `TauCeti.jetShift`: forgetting the top entry of a jet, and shifting a jet
  down by one in a direction `h`.
* `TauCeti.Jet`: a scope of shortcut instances for spaces of jets and of continuous linear maps
  between them, to be opened by files working with jets.
* `ContinuousLinearMap.leibnizJet`: the Leibniz map from the jets of two maps to the derivatives
  of their bilinear product.
* `ContinuousLinearMap.curryLeft_leibnizJet_succ`: its defining recursion.
* `ContinuousLinearMap.norm_leibnizJet_le`: the bound `‖leibnizJet B E n‖ ≤ 2ⁿ ‖B‖`.
* `ContinuousLinearMap.hasFDerivAt_leibnizJet`: differentiating `leibnizJet B E n` along
  families of jets.
* `ContinuousLinearMap.iteratedFDeriv_bilinear_eq_leibnizJet`: the Leibniz rule
  `Dⁿ (B (f, g)) = leibnizJet B E n (D^• f) (D^• g)`.
* `ContinuousLinearMap.leibnizJet_succ_apply_const_of_forall_lt_eq_zero`: if `J₀ = 0` and the
  entries of `K` of order below `n` vanish, then on the diagonal
  `leibnizJet B E (n + 1) J K (h, …, h) = (n + 1) • B (J₁ h) (Kₙ (h, …, h))`.
* `TauCeti.iteratedFDeriv_prod_smul_apply_const`: a product `f₁ ⋯ fᵣ • u` of `r` functions
  vanishing at `x` with a map `u` vanishes to order `r` at `x`
  (`TauCeti.iteratedFDeriv_prod_smul_eq_zero_of_lt`), and its derivative of order `r` there is
  `r! • (∏ᵢ Dfᵢ(x) h) • u x` on the diagonal `(h, …, h)`.
-/

public section

noncomputable section

variable {𝕜 E F G H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H] [NormedSpace 𝕜 H]

namespace TauCeti.Jet

variable (𝕜 E) in
/-- Shortcut instance for jets of multilinear maps: without it, instance search for spaces of
continuous linear maps between spaces of jets exceeds the default synthesis depth. -/
scoped instance instNormedAddCommGroupJet (X : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (m : ℕ) : NormedAddCommGroup ((i : Fin m) → E [×i]→L[𝕜] X) :=
  inferInstance

variable (𝕜 E) in
/-- Shortcut instance for scalar operations on jets of multilinear maps. -/
scoped instance instNormedSpaceJet (X : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (m : ℕ) : NormedSpace 𝕜 ((i : Fin m) → E [×i]→L[𝕜] X) :=
  inferInstance

variable (𝕜 E) in
/-- Shortcut instance for continuous linear maps from jets to multilinear maps. -/
scoped instance instNormedAddCommGroupJetCLM (X Y : Type*) [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (m n : ℕ) :
    NormedAddCommGroup (((i : Fin m) → E [×i]→L[𝕜] X) →L[𝕜] E [×n]→L[𝕜] Y) :=
  inferInstance

variable (𝕜 E) in
/-- Shortcut instance for scalar operations on continuous linear maps from jets to multilinear
maps. -/
scoped instance instNormedSpaceJetCLM (X Y : Type*) [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (m n : ℕ) :
    NormedSpace 𝕜 (((i : Fin m) → E [×i]→L[𝕜] X) →L[𝕜] E [×n]→L[𝕜] Y) :=
  inferInstance

end TauCeti.Jet

open scoped TauCeti.Jet

namespace TauCeti

variable (𝕜 E F) in
/-- The jet `(J₀, …, Jₙ)` of order `n + 1` with its top entry forgotten. -/
def jetInit (n : ℕ) :
    ((i : Fin (n + 2)) → E [×i]→L[𝕜] F) →L[𝕜] ((i : Fin (n + 1)) → E [×i]→L[𝕜] F) :=
  ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj i.castSucc

@[simp]
theorem jetInit_apply (n : ℕ) (J : (i : Fin (n + 2)) → E [×i]→L[𝕜] F) (i : Fin (n + 1)) :
    jetInit 𝕜 E F n J i = J i.castSucc :=
  (rfl)

/-- Forgetting the top entry of the jet `(φ i)ᵢ` of a family indexed by all orders `i : ℕ` gives
its jet one order lower. -/
theorem jetInit_fun_coe (n : ℕ) (φ : (i : ℕ) → E [×i]→L[𝕜] F) :
    jetInit 𝕜 E F n (fun i : Fin (n + 2) ↦ φ i) = fun i : Fin (n + 1) ↦ φ i :=
  -- The entry `φ (i.castSucc : ℕ)` is `φ (i : ℕ)`, since `Fin.val_castSucc` holds by definition;
  -- `simp` cannot rewrite the index, on which the type of `φ` depends.
  funext fun i ↦ jetInit_apply n _ i

/-- The shift of a jet of order `n + 1` in a direction `h`: the jet of order `n` with entries
`Jᵢ₊₁ (h, ·)`, the first variable of `Jᵢ₊₁` being set to `h`. -/
private def jetShiftAux (n : ℕ) :
    ((i : Fin (n + 2)) → E [×i]→L[𝕜] F) →ₗ[𝕜] E →ₗ[𝕜] ((i : Fin (n + 1)) → E [×i]→L[𝕜] F) :=
  LinearMap.mk₂ 𝕜 (fun J h i ↦ (J i.succ).curryLeft h)
    (fun _ _ _ ↦ by ext; simp)
    (fun _ _ _ ↦ by ext; simp)
    (fun _ _ _ ↦ by ext; simp)
    (fun _ _ _ ↦ by ext; simp)

variable (𝕜 E F) in
/-- The shift of a jet of order `n + 1` in a direction `h`: the jet of order `n` with entries
`Jᵢ₊₁ (h, ·)`. For the jet of iterated derivatives of a map, this is the jet of the derivative in
the direction `h`. -/
def jetShift (n : ℕ) :
    ((i : Fin (n + 2)) → E [×i]→L[𝕜] F) →L[𝕜] E →L[𝕜] ((i : Fin (n + 1)) → E [×i]→L[𝕜] F) :=
  (jetShiftAux n).mkContinuous₂ 1 fun J h ↦ by
    rw [one_mul]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
    -- The `i`-th entry of the shift is `(J i.succ).curryLeft h` by the definition of
    -- `jetShiftAux`; `LinearMap.mk₂_apply` does not see through the bundled family.
    change ‖(J i.succ).curryLeft h‖ ≤ ‖J‖ * ‖h‖
    exact ((J i.succ).curryLeft.le_opNorm h).trans (by
      rw [ContinuousMultilinearMap.curryLeft_norm]
      gcongr
      exact norm_le_pi_norm J i.succ)

@[simp]
theorem jetShift_apply (n : ℕ) (J : (i : Fin (n + 2)) → E [×i]→L[𝕜] F) (h : E) (i : Fin (n + 1)) :
    jetShift 𝕜 E F n J h i = (J i.succ).curryLeft h :=
  (rfl)

/-- Forgetting the top entry does not increase the norm of a jet. -/
theorem norm_jetInit_apply_le (n : ℕ) (J : (i : Fin (n + 2)) → E [×i]→L[𝕜] F) :
    ‖jetInit 𝕜 E F n J‖ ≤ ‖J‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg J)).2 fun i ↦ norm_le_pi_norm J i.castSucc

/-- The shift has norm at most `1`. -/
theorem norm_jetShift_le (n : ℕ) : ‖jetShift 𝕜 E F n‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

/-- The shift of a jet in a direction `h` is bounded by `‖J‖ ‖h‖`. -/
theorem norm_jetShift_apply_apply_le (n : ℕ) (J : (i : Fin (n + 2)) → E [×i]→L[𝕜] F) (h : E) :
    ‖jetShift 𝕜 E F n J h‖ ≤ ‖J‖ * ‖h‖ :=
  ((jetShift 𝕜 E F n).le_opNorm₂ J h).trans (by
    gcongr
    exact mul_le_of_le_one_left (norm_nonneg J) (norm_jetShift_le n))

/-- As a continuous linear map in the direction, the shift of `J` is the family of the entries
`Jᵢ₊₁`, curried on the left. -/
theorem jetShift_apply_eq_pi (n : ℕ) (J : (i : Fin (n + 2)) → E [×i]→L[𝕜] F) :
    jetShift 𝕜 E F n J = ContinuousLinearMap.pi fun i ↦ (J i.succ).curryLeft :=
  ContinuousLinearMap.ext fun h ↦ funext fun i ↦ by simp

/-- If the entries of `K` of order below `k + 1` vanish, then so do the entries of order below `k`
of its shift `∂ₕ K`. -/
theorem jetShift_apply_eq_zero_of_forall_lt {n k : ℕ} {K : (i : Fin (n + 2)) → E [×i]→L[𝕜] F}
    (hK : ∀ i : Fin (n + 2), i.val < k + 1 → K i = 0) (h : E) {i : Fin (n + 1)}
    (hi : i.val < k) : jetShift 𝕜 E F n K h i = 0 := by
  rw [jetShift_apply, hK i.succ (by simpa using hi)]
  ext
  simp

/-- The shift of a jet in a direction `h`, at order zero, is its entry of order one at `h`. -/
theorem jetShift_apply_zero_apply {n : ℕ} (J : (i : Fin (n + 2)) → E [×i]→L[𝕜] F)
    (h : E) : jetShift 𝕜 E F n J h 0 0 = J 1 fun _ ↦ h := by
  rw [jetShift_apply, ContinuousMultilinearMap.curryLeft_apply]
  exact congrArg (J 1) (funext fun i ↦ Fin.cases rfl (fun j ↦ j.elim0) i)

end TauCeti

open TauCeti

namespace ContinuousLinearMap

variable (B : F →L[𝕜] G →L[𝕜] H)

/-- The order-zero Leibniz map `(J, K) ↦ B J₀ K₀`. -/
private def leibnizJetZero :
    ((i : Fin 1) → E [×i]→L[𝕜] F) →L[𝕜] ((i : Fin 1) → E [×i]→L[𝕜] G) →L[𝕜] E [×0]→L[𝕜] H :=
  (LinearMap.mk₂ 𝕜
    (fun J K ↦ (continuousMultilinearCurryFin0 𝕜 E H).symm
      (B (continuousMultilinearCurryFin0 𝕜 E F (J 0))
        (continuousMultilinearCurryFin0 𝕜 E G (K 0))))
    (fun _ _ _ ↦ by simp only [Pi.add_apply, map_add, add_apply])
    (fun _ _ _ ↦ by simp only [Pi.smul_apply, map_smul, smul_apply])
    (fun _ _ _ ↦ by simp only [Pi.add_apply, map_add])
    (fun _ _ _ ↦ by simp only [Pi.smul_apply, map_smul])).mkContinuous₂ ‖B‖ fun J K ↦ by
    simp only [LinearMap.mk₂_apply, LinearIsometryEquiv.norm_map]
    refine (B.le_opNorm₂ _ _).trans ?_
    rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
    gcongr
    · exact norm_le_pi_norm J 0
    · exact norm_le_pi_norm K 0

/-- The inner linear map of the recursion step, before uncurrying:
`h ↦ L (∂ₕ J) (init K) + L (init J) (∂ₕ K)`. -/
private def leibnizJetStep {n : ℕ}
    (L : ((i : Fin (n + 1)) → E [×i]→L[𝕜] F) →L[𝕜] ((i : Fin (n + 1)) → E [×i]→L[𝕜] G) →L[𝕜]
      E [×n]→L[𝕜] H)
    (J : (i : Fin (n + 2)) → E [×i]→L[𝕜] F) (K : (i : Fin (n + 2)) → E [×i]→L[𝕜] G) :
    E →L[𝕜] E [×n]→L[𝕜] H :=
  (L.flip (jetInit 𝕜 E G n K)).comp (jetShift 𝕜 E F n J) +
    (L (jetInit 𝕜 E F n J)).comp (jetShift 𝕜 E G n K)

private theorem leibnizJetStep_apply {n : ℕ}
    (L : ((i : Fin (n + 1)) → E [×i]→L[𝕜] F) →L[𝕜] ((i : Fin (n + 1)) → E [×i]→L[𝕜] G) →L[𝕜]
      E [×n]→L[𝕜] H)
    (J : (i : Fin (n + 2)) → E [×i]→L[𝕜] F) (K : (i : Fin (n + 2)) → E [×i]→L[𝕜] G) (h : E) :
    leibnizJetStep L J K h =
      L (jetShift 𝕜 E F n J h) (jetInit 𝕜 E G n K) +
        L (jetInit 𝕜 E F n J) (jetShift 𝕜 E G n K h) :=
  rfl

private theorem norm_leibnizJetStep_le {n : ℕ}
    (L : ((i : Fin (n + 1)) → E [×i]→L[𝕜] F) →L[𝕜] ((i : Fin (n + 1)) → E [×i]→L[𝕜] G) →L[𝕜]
      E [×n]→L[𝕜] H)
    (J : (i : Fin (n + 2)) → E [×i]→L[𝕜] F) (K : (i : Fin (n + 2)) → E [×i]→L[𝕜] G) :
    ‖leibnizJetStep L J K‖ ≤ 2 * ‖L‖ * ‖J‖ * ‖K‖ := by
  refine opNorm_le_bound _ (by positivity) fun h ↦ ?_
  rw [leibnizJetStep_apply]
  refine (norm_add_le _ _).trans ?_
  have h₁ := (L.le_opNorm₂ (jetShift 𝕜 E F n J h) (jetInit 𝕜 E G n K)).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left (norm_jetShift_apply_apply_le n J h) (norm_nonneg L))
      (norm_jetInit_apply_le n K) (norm_nonneg _) (by positivity))
  have h₂ := (L.le_opNorm₂ (jetInit 𝕜 E F n J) (jetShift 𝕜 E G n K h)).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left (norm_jetInit_apply_le n J) (norm_nonneg L))
      (norm_jetShift_apply_apply_le n K h) (norm_nonneg _) (by positivity))
  nlinarith [h₁, h₂, norm_nonneg L, norm_nonneg J, norm_nonneg K, norm_nonneg h]

/-- The Leibniz map of order `n`: the continuous bilinear map sending the jets of order `n` of two
maps `f` and `g` at a point to the `n`-th derivative of `y ↦ B (f y) (g y)` there
(`ContinuousLinearMap.iteratedFDeriv_bilinear_eq_leibnizJet`). -/
def leibnizJet (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    (n : ℕ) → ((i : Fin (n + 1)) → E [×i]→L[𝕜] F) →L[𝕜]
      ((i : Fin (n + 1)) → E [×i]→L[𝕜] G) →L[𝕜] E [×n]→L[𝕜] H
  | 0 => leibnizJetZero B
  | n + 1 =>
    (LinearMap.mk₂ 𝕜
      (fun J K ↦ (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) ↦ E) H).symm
        (leibnizJetStep (leibnizJet E n) J K))
      (fun _ _ _ ↦ by
        rw [← map_add]
        congr 1
        ext h
        simp [leibnizJetStep_apply]
        abel)
      (fun _ _ _ ↦ by
        rw [← map_smul]
        congr 1
        ext h
        simp [leibnizJetStep_apply])
      (fun _ _ _ ↦ by
        rw [← map_add]
        congr 1
        ext h
        simp [leibnizJetStep_apply]
        abel)
      (fun _ _ _ ↦ by
        rw [← map_smul]
        congr 1
        ext h
        simp [leibnizJetStep_apply])).mkContinuous₂ (2 * ‖leibnizJet E n‖) fun J K ↦ by
      simp only [LinearMap.mk₂_apply, LinearIsometryEquiv.norm_map]
      exact norm_leibnizJetStep_le _ J K

/-- The Leibniz map of order zero is `(J, K) ↦ B J₀ K₀`. -/
@[simp]
theorem leibnizJet_zero_apply_apply (J : (i : Fin 1) → E [×i]→L[𝕜] F)
    (K : (i : Fin 1) → E [×i]→L[𝕜] G) (v : Fin 0 → E) :
    leibnizJet B E 0 J K v = B (J 0 0) (K 0 0) :=
  (rfl)

/-- **The Leibniz recursion.** The Leibniz map of order `n + 1`, curried on the left at `h`, is
`leibnizJet B E n (∂ₕ J) (init K) + leibnizJet B E n (init J) (∂ₕ K)`. -/
@[simp]
theorem curryLeft_leibnizJet_succ {n : ℕ} (J : (i : Fin (n + 2)) → E [×i]→L[𝕜] F)
    (K : (i : Fin (n + 2)) → E [×i]→L[𝕜] G) (h : E) :
    (leibnizJet B E (n + 1) J K).curryLeft h =
      leibnizJet B E n (jetShift 𝕜 E F n J h) (jetInit 𝕜 E G n K) +
        leibnizJet B E n (jetInit 𝕜 E F n J) (jetShift 𝕜 E G n K h) := by
  -- By definition, `leibnizJet B E (n + 1) J K` is the uncurrying of the recursion step, and
  -- `curryLeft` is the currying equivalence; the step is recovered by `apply_symm_apply`.
  change continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) ↦ E) H
    ((continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) ↦ E) H).symm
      (leibnizJetStep (leibnizJet B E n) J K)) h = _
  rw [LinearIsometryEquiv.apply_symm_apply, leibnizJetStep_apply]

/-- The Leibniz map of order `n` has norm at most `2ⁿ ‖B‖`. -/
theorem norm_leibnizJet_le (n : ℕ) : ‖leibnizJet B E n‖ ≤ 2 ^ n * ‖B‖ := by
  induction n with
  | zero =>
    rw [pow_zero, one_mul, leibnizJet]
    exact LinearMap.mkContinuous₂_norm_le _ (norm_nonneg B) _
  | succ n ih =>
    rw [leibnizJet]
    refine (LinearMap.mkContinuous₂_norm_le _ (by positivity) _).trans ?_
    rw [pow_succ]
    nlinarith [norm_nonneg B]

/-- **Differentiating the Leibniz map along jets.** Let `f, g : E → jets of order n + 1` be such
that each entry of order at most `n` has derivative `D fᵢ (x) h = fᵢ₊₁ (x) (h, ·)`, and likewise
for `g`. Then `y ↦ leibnizJet B E n (init (f y)) (init (g y))` has derivative
`leibnizJet B E (n + 1) (f x) (g x)`, curried on the left. -/
theorem hasFDerivAt_leibnizJet {n : ℕ} {f : E → (i : Fin (n + 2)) → E [×i]→L[𝕜] F}
    {g : E → (i : Fin (n + 2)) → E [×i]→L[𝕜] G} {x : E}
    (hf : ∀ i : Fin (n + 1), HasFDerivAt (fun y ↦ f y i.castSucc) (f x i.succ).curryLeft x)
    (hg : ∀ i : Fin (n + 1), HasFDerivAt (fun y ↦ g y i.castSucc) (g x i.succ).curryLeft x) :
    HasFDerivAt (fun y ↦ leibnizJet B E n (jetInit 𝕜 E F n (f y)) (jetInit 𝕜 E G n (g y)))
      (leibnizJet B E (n + 1) (f x) (g x)).curryLeft x := by
  have hf' : HasFDerivAt (fun y ↦ jetInit 𝕜 E F n (f y)) (jetShift 𝕜 E F n (f x)) x :=
    (jetShift_apply_eq_pi n (f x)) ▸ hasFDerivAt_pi.2 hf
  have hg' : HasFDerivAt (fun y ↦ jetInit 𝕜 E G n (g y)) (jetShift 𝕜 E G n (g x)) x :=
    (jetShift_apply_eq_pi n (g x)) ▸ hasFDerivAt_pi.2 hg
  refine ((leibnizJet B E n).hasFDerivAt_of_bilinear hf' hg').congr_fderiv ?_
  ext1 h
  rw [curryLeft_leibnizJet_succ, add_comm]
  simp only [add_apply, precompR_apply, precompL_apply, compL_apply, comp_apply]

/-- **The Leibniz rule.** For `n` times continuously differentiable maps `f` and `g`, the `m`-th
derivative of `y ↦ B (f y) (g y)`, `m ≤ n`, is the Leibniz map of order `m` applied to the jets
`(Dⁱ f (x))ᵢ` and `(Dⁱ g (x))ᵢ`. -/
theorem iteratedFDeriv_bilinear_eq_leibnizJet {n : WithTop ℕ∞} {f : E → F} {g : E → G}
    (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) {m : ℕ} (hm : m ≤ n) (x : E) :
    iteratedFDeriv 𝕜 m (fun y ↦ B (f y) (g y)) x =
      leibnizJet B E m (fun i ↦ iteratedFDeriv 𝕜 i f x) (fun i ↦ iteratedFDeriv 𝕜 i g x) := by
  induction m generalizing x with
  | zero =>
    ext v
    simp
  | succ m ih =>
    have hm' : (m : WithTop ℕ∞) < n :=
      lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self m) hm
    have hi : ∀ i : Fin (m + 1), ((i : ℕ) : WithTop ℕ∞) < n := fun i ↦
      lt_of_le_of_lt (by exact_mod_cast Nat.lt_succ_iff.1 i.isLt) hm'
    have hD := hasFDerivAt_leibnizJet B (n := m) (x := x)
      (f := fun y (i : Fin (m + 2)) ↦ iteratedFDeriv 𝕜 i f y)
      (g := fun y (i : Fin (m + 2)) ↦ iteratedFDeriv 𝕜 i g y)
      (fun i ↦ hf.ftaylorSeries.fderiv i (hi i) x)
      (fun i ↦ hg.ftaylorSeries.fderiv i (hi i) x)
    have hfun : iteratedFDeriv 𝕜 m (fun y ↦ B (f y) (g y)) = fun y ↦
        leibnizJet B E m (jetInit 𝕜 E F m fun i : Fin (m + 2) ↦ iteratedFDeriv 𝕜 i f y)
          (jetInit 𝕜 E G m fun i : Fin (m + 2) ↦ iteratedFDeriv 𝕜 i g y) :=
      funext fun y ↦ by
        rw [jetInit_fun_coe m fun i ↦ iteratedFDeriv 𝕜 i f y,
          jetInit_fun_coe m fun i ↦ iteratedFDeriv 𝕜 i g y]
        exact ih (le_trans (by exact_mod_cast Nat.le_succ m) hm) y
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hfun, hD.fderiv]
    exact ContinuousMultilinearMap.uncurry_curryLeft _

/-! ### Jets vanishing below a given order -/

/-- If the entries of `K` of order below `n` vanish, then on the diagonal the Leibniz map of order
`n` is `B J₀ (Kₙ (h, …, h))`: every other term of the Leibniz rule differentiates `K` fewer than
`n` times. -/
theorem leibnizJet_apply_const_of_forall_lt_eq_zero {n : ℕ}
    (J : (i : Fin (n + 1)) → E [×i]→L[𝕜] F) {K : (i : Fin (n + 1)) → E [×i]→L[𝕜] G}
    (hK : ∀ i : Fin (n + 1), i.val < n → K i = 0) (h : E) :
    leibnizJet B E n J K (fun _ ↦ h) = B (J 0 0) (K (Fin.last n) fun _ ↦ h) := by
  induction n with
  | zero =>
    rw [leibnizJet_zero_apply_apply]
    exact congrArg _ (congrArg _ (Subsingleton.elim (α := Fin 0 → E) _ _))
  | succ n ih =>
    have hinit : jetInit 𝕜 E G n K = 0 :=
      funext fun i ↦ hK i.castSucc (by simp only [Fin.val_castSucc]; exact i.isLt)
    rw [ContinuousMultilinearMap.apply_const_eq_curryLeft, curryLeft_leibnizJet_succ, hinit,
      map_zero, zero_add, ih (jetInit 𝕜 E F n J) (K := jetShift 𝕜 E G n K h)
        (fun i hi ↦ jetShift_apply_eq_zero_of_forall_lt hK h hi)]
    -- `init J` at order `0` is `J 0`, and `∂ₕ K` at order `n` is `K (n + 1)` curried at `h`.
    exact congrArg (B (J 0 0)) (ContinuousMultilinearMap.apply_const_eq_curryLeft _ h).symm

/-- **The leading term of the Leibniz rule.** If `J₀ = 0` and the entries of `K` of order below
`n` vanish, then on the diagonal the Leibniz map of order `n + 1` is
`(n + 1) • B (J₁ h) (Kₙ (h, …, h))`: the only surviving terms differentiate `J` once and `K`
`n` times, and there are `n + 1` of them. -/
theorem leibnizJet_succ_apply_const_of_forall_lt_eq_zero {n : ℕ}
    {J : (i : Fin (n + 2)) → E [×i]→L[𝕜] F} {K : (i : Fin (n + 2)) → E [×i]→L[𝕜] G}
    (hJ : J 0 = 0) (hK : ∀ i : Fin (n + 2), i.val < n → K i = 0) (h : E) :
    leibnizJet B E (n + 1) J K (fun _ ↦ h) =
      (n + 1) • B (J 1 fun _ ↦ h) (K (Fin.last n).castSucc fun _ ↦ h) := by
  -- In the recursion, the first term differentiates `J` once and is one copy of the leading term;
  -- the second term starts from `init J`, whose entry of order zero is `J₀ = 0`, and gives the
  -- other `n` copies, by induction.
  induction n with
  | zero => ?_
  | succ n ih => ?_
  all_goals
    rw [ContinuousMultilinearMap.apply_const_eq_curryLeft, curryLeft_leibnizJet_succ, add_apply,
      leibnizJet_apply_const_of_forall_lt_eq_zero B _ (K := jetInit 𝕜 E G _ K)
        (fun i hi ↦ hK i.castSucc hi) h,
      jetShift_apply_zero_apply, jetInit_apply, succ_nsmul']
    congr 1
    -- `init J` at order `0` is `J (Fin.castSucc 0)`, which is `J 0` by definition; rewriting
    -- along `Fin.castSucc_zero` is blocked because the type of `J i` depends on `i`.
    have hJ' : jetInit 𝕜 E F _ J 0 = 0 := hJ
  · rw [leibnizJet_zero_apply_apply, hJ']
    simp
  · rw [ih hJ' (fun i hi ↦ jetShift_apply_eq_zero_of_forall_lt hK h hi),
      jetShift_apply, ← ContinuousMultilinearMap.apply_const_eq_curryLeft]
    -- `init J` at order `1` is `J (Fin.castSucc 1)`, and `∂ₕ K` at order `n` is
    -- `K (Fin.last n).castSucc.succ`. These are `J 1` and `K (Fin.last (n + 1)).castSucc` by
    -- definition; as above, rewriting along `Fin.castSucc_one` and `Fin.succ_castSucc` is blocked
    -- because the types of `J i` and `K i` depend on `i`.
    rfl

end ContinuousLinearMap

namespace TauCeti

/-! ### Products of functions vanishing at a point -/

/-- **The first nonvanishing derivative of a product.** If `f x = 0` and the derivatives of `g` of
order below `n` vanish at `x`, then the derivative of order `n + 1` of `f • g` at `x` is, on the
diagonal, `(n + 1) • (Df(x) h • Dⁿg(x) (h, …, h))`. -/
theorem iteratedFDeriv_smul_apply_const_of_eq_zero {n : ℕ} {f : E → 𝕜} {g : E → F}
    (hf : ContDiff 𝕜 (n + 1) f) (hg : ContDiff 𝕜 (n + 1) g) {x : E} (hfx : f x = 0)
    (hgx : ∀ i < n, iteratedFDeriv 𝕜 i g x = 0) (h : E) :
    iteratedFDeriv 𝕜 (n + 1) (fun y ↦ f y • g y) x (fun _ ↦ h) =
      (n + 1) • (fderiv 𝕜 f x h • iteratedFDeriv 𝕜 n g x fun _ ↦ h) := by
  have hB := (ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] F →L[𝕜] F)
    |>.iteratedFDeriv_bilinear_eq_leibnizJet hf hg (m := n + 1) (by exact_mod_cast le_rfl) x
  simp only [ContinuousLinearMap.lsmul_apply] at hB
  rw [hB, ContinuousLinearMap.leibnizJet_succ_apply_const_of_forall_lt_eq_zero _ (by
      ext m
      exact (iteratedFDeriv_zero_apply m).trans hfx)
    (fun i hi ↦ hgx i hi), Fin.val_one, iteratedFDeriv_one_apply, Fin.val_castSucc, Fin.val_last,
    ContinuousLinearMap.lsmul_apply]

/-- **The first nonvanishing derivative of a product of vanishing functions.** If `f₁, …, fᵣ`
vanish at `x`, the derivative of order `r` of `f₁ ⋯ fᵣ • u` at `x` is, on the diagonal,
`r! • (∏ᵢ Dfᵢ(x) h) • u x`. -/
theorem iteratedFDeriv_prod_smul_apply_const {r : ℕ} {f : Fin r → E → 𝕜} {u : E → F}
    (hf : ∀ i, ContDiff 𝕜 r (f i)) (hu : ContDiff 𝕜 r u) {x : E} (hfx : ∀ i, f i x = 0)
    (h : E) :
    iteratedFDeriv 𝕜 r (fun y ↦ (∏ i, f i y) • u y) x (fun _ ↦ h) =
      r.factorial • ((∏ i, fderiv 𝕜 (f i) x h) • u x) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hfun : (fun y ↦ (∏ i, f i y) • u y) =
        fun y ↦ f 0 y • ((∏ i : Fin r, f i.succ y) • u y) := by
      funext y
      rw [Fin.prod_univ_succ, mul_smul]
    have hle : (r : WithTop ℕ∞) ≤ ((r + 1 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast Nat.le_succ r
    have hrest : ContDiff 𝕜 (r + 1) fun y ↦ (∏ i : Fin r, f i.succ y) • u y := by
      exact_mod_cast (contDiff_prod fun (i : Fin r) _ ↦ hf i.succ).smul hu
    rw [hfun, iteratedFDeriv_smul_apply_const_of_eq_zero (by exact_mod_cast hf 0) hrest (hfx 0)
      (fun i hi ↦ iteratedFDeriv_prod_smul_eq_zero_of_lt (f := fun j ↦ f j.succ)
        (fun j ↦ ((hf j.succ).of_le hle).contDiffAt) (hu.of_le hle).contDiffAt
        (fun j ↦ hfx j.succ) hi),
      ih (f := fun j ↦ f j.succ) (fun j ↦ (hf j.succ).of_le hle) (hu.of_le hle)
        (fun j ↦ hfx j.succ),
      Fin.prod_univ_succ, Nat.factorial_succ, mul_smul, mul_smul,
      smul_comm (fderiv 𝕜 (f 0) x h) r.factorial]

end TauCeti
