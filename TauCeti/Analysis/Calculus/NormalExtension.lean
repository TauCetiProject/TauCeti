/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Analysis.Calculus.ContDiff.TendstoAt
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap

/-!
# Normal extensions for adapted coordinates

The map `normalExtension γ A (x, y) = γ x + A x y` extends a parametrization by prescribed
normal directions. Its derivative on the zero section requires only continuity of the normal
frame, rather than differentiability of that frame.

The adapted extension uses `A x = J (γ x) ∘ Dγ x`. If `γ` is `C^(n+1)` and `J` is `C^n`, this
extension is `C^n`, including finite orders. The ambient almost complex field is given by its
continuous-linear endomorphisms in coordinates. These extensions are candidate charts for
coordinates adapted to a totally real submanifold.

## Main declarations

* `normalExtension`: a parametrization extended by a prescribed normal frame.
* `hasFDerivAt_normalExtension_zero`: its first jet for merely continuous normal frames.
* `adaptedNormalExtension`: the frame obtained by applying `J` to the tangential derivative.
* `contDiffOn_adaptedNormalExtension`: finite regularity on open coordinate domains.
* `fderiv_adaptedNormalExtension_intertwines`: complex linearity of the adapted first jet.
* `tendstoContDiffAt_adaptedNormalExtension`: `C^ℓ` convergence of the adapted extensions for
  structures converging in `C^ℓ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Exercise B.4.10.
-/

public noncomputable section

open scoped Topology ContDiff

namespace TauCeti

variable {𝕜 V W E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Extend a parametrization by a prescribed family of normal directions. -/
def normalExtension (γ : V → W) (A : V → E →L[𝕜] W) (p : V × E) : W :=
  γ p.1 + A p.1 p.2

omit [NormedAddCommGroup V] [NormedSpace 𝕜 V] in
/-- Evaluate a normal extension at an arbitrary point. -/
@[simp]
theorem normalExtension_apply (γ : V → W) (A : V → E →L[𝕜] W) (p : V × E) :
    normalExtension γ A p = γ p.1 + A p.1 p.2 := by rfl

omit [NormedAddCommGroup V] [NormedSpace 𝕜 V] in
/-- The extension agrees with its parametrization on the zero section. -/
theorem normalExtension_zero (γ : V → W) (A : V → E →L[𝕜] W) (x : V) :
    normalExtension γ A (x, 0) = γ x := by simp [normalExtension]

/-- The normal extension has the common regularity of its parametrization and its frame. -/
theorem contDiff_normalExtension {γ : V → W} {A : V → E →L[𝕜] W} {n : ℕ∞ω}
    (hγ : ContDiff 𝕜 n γ) (hA : ContDiff 𝕜 n A) :
    ContDiff 𝕜 n (normalExtension γ A) :=
  (hγ.comp contDiff_fst).add ((hA.comp contDiff_fst).clm_apply contDiff_snd)

/-- Regularity of the extension is local in its tangential variable. -/
theorem contDiffAt_normalExtension {γ : V → W} {A : V → E →L[𝕜] W} {n : ℕ∞ω}
    {x : V} {y : E} (hγ : ContDiffAt 𝕜 n γ x) (hA : ContDiffAt 𝕜 n A x) :
    ContDiffAt 𝕜 n (normalExtension γ A) (x, y) :=
  (hγ.comp (x, y) contDiffAt_fst).add
    ((hA.comp (x, y) contDiffAt_fst).clm_apply contDiffAt_snd)

/-- On the zero section, continuity of the normal frame suffices for the first-jet formula.
No derivative of that frame is required. -/
theorem hasFDerivAt_normalExtension_zero {γ : V → W} {A : V → E →L[𝕜] W} {x : V}
    {D : V →L[𝕜] W} (hγ : HasFDerivAt γ D x) (hA : ContinuousAt A x) :
    HasFDerivAt (normalExtension γ A) (D.coprod (A x)) (x, 0) := by
  have hAc : ContinuousWithinAt (fun p : V × E ↦ A p.1) Set.univ (x, 0) :=
    (hA.comp continuousAt_fst).continuousWithinAt
  have hnormal := (HasFDerivWithinAt.clm_apply_of_eq_zero hAc
    (hasFDerivAt_snd.hasFDerivWithinAt) rfl).hasFDerivAt_of_univ
  exact ((hγ.comp (x, 0) hasFDerivAt_fst).add hnormal).congr_fderiv
    (ContinuousLinearMap.ext fun p ↦ by simp [ContinuousLinearMap.coprod_apply])

/-- The derivative of a normal extension along the zero section is its doubled frame. -/
theorem fderiv_normalExtension_zero {γ : V → W} {A : V → E →L[𝕜] W} {x : V}
    (hγ : DifferentiableAt 𝕜 γ x) (hA : ContinuousAt A x) :
    fderiv 𝕜 (normalExtension γ A) (x, 0) = (fderiv 𝕜 γ x).coprod (A x) :=
  (hasFDerivAt_normalExtension_zero hγ.hasFDerivAt hA).fderiv

/-- The normal extension used to build coordinates adapted to a totally real submanifold. -/
def adaptedNormalExtension (γ : V → W) (J : W → W →L[𝕜] W) : V × V → W :=
  normalExtension γ (fun x ↦ (J (γ x)).comp (fderiv 𝕜 γ x))

/-- Express the adapted extension through its prescribed normal frame. -/
theorem adaptedNormalExtension_eq_normalExtension (γ : V → W) (J : W → W →L[𝕜] W) :
    adaptedNormalExtension γ J =
      normalExtension γ (fun x ↦ (J (γ x)).comp (fderiv 𝕜 γ x)) := by rfl

/-- Evaluate an adapted normal extension at an arbitrary point. -/
@[simp]
theorem adaptedNormalExtension_apply (γ : V → W) (J : W → W →L[𝕜] W) (p : V × V) :
    adaptedNormalExtension γ J p = γ p.1 + J (γ p.1) (fderiv 𝕜 γ p.1 p.2) := by rfl

/-- The adapted extension agrees with the parametrized submanifold. -/
theorem adaptedNormalExtension_zero (γ : V → W) (J : W → W →L[𝕜] W) (x : V) :
    adaptedNormalExtension γ J (x, 0) = γ x := by
  simp [adaptedNormalExtension]

/-- The adapted extension is `C^n` for a `C^(n+1)` parametrization and `C^n` structure.
In particular a smooth parametrization costs no derivative of the almost complex field. -/
theorem contDiff_adaptedNormalExtension {γ : V → W} {J : W → W →L[𝕜] W} {n : ℕ∞ω}
    (hγ : ContDiff 𝕜 (n + 1) γ) (hJ : ContDiff 𝕜 n J) :
    ContDiff 𝕜 n (adaptedNormalExtension γ J) := by
  have hγn := hγ.of_le (le_self_add : n ≤ n + 1)
  exact contDiff_normalExtension hγn ((hJ.comp hγn).clm_comp (hγ.fderiv_right le_rfl))

/-- The local regularity statement, suitable for coordinate domains. -/
theorem contDiffAt_adaptedNormalExtension {γ : V → W} {J : W → W →L[𝕜] W} {n : ℕ∞ω}
    {x y : V} (hγ : ContDiffAt 𝕜 (n + 1) γ x) (hJ : ContDiffAt 𝕜 n J (γ x)) :
    ContDiffAt 𝕜 n (adaptedNormalExtension γ J) (x, y) := by
  have hγn := hγ.of_le (le_self_add : n ≤ n + 1)
  exact contDiffAt_normalExtension hγn
    ((hJ.comp x hγn).clm_comp (hγ.fderiv_right le_rfl))

/-- If `γ` is `C^(n+1)` on an open `U` and maps it into any set `Ω` on which `J` is `C^n`,
the adapted extension is `C^n` on `U ×ˢ univ`. No openness of `Ω` is required. -/
theorem contDiffOn_adaptedNormalExtension {γ : V → W} {J : W → W →L[𝕜] W} {n : ℕ∞ω}
    {U : Set V} {Ω : Set W} (hU : IsOpen U)
    (hγ : ContDiffOn 𝕜 (n + 1) γ U) (hJ : ContDiffOn 𝕜 n J Ω)
    (hγΩ : Set.MapsTo γ U Ω) :
    ContDiffOn 𝕜 n (adaptedNormalExtension γ J) (U ×ˢ Set.univ) := by
  have hγn := hγ.of_le (le_self_add : n ≤ n + 1)
  have hA := (hJ.comp hγn hγΩ).clm_comp (hγ.fderiv_of_isOpen hU le_rfl)
  have hfst : Set.MapsTo (Prod.fst : V × V → V) (U ×ˢ Set.univ) U := fun _ hp ↦ hp.1
  exact ((hγn.comp contDiffOn_fst hfst).add
    ((hA.comp contDiffOn_fst hfst).clm_apply contDiffOn_snd)).congr
      (fun p _ ↦ by simp only [adaptedNormalExtension_apply, Function.comp_apply,
        ContinuousLinearMap.comp_apply])

/-- The adapted first jet requires only a `C^1` parametrization and a continuous structure
at the base point. In particular it does not consume a derivative of `J`. -/
theorem hasFDerivAt_adaptedNormalExtension_zero {γ : V → W} {J : W → W →L[𝕜] W} {x : V}
    (hγ : ContDiffAt 𝕜 1 γ x) (hJ : ContinuousAt J (γ x)) :
    HasFDerivAt (adaptedNormalExtension γ J)
      ((fderiv 𝕜 γ x).coprod ((J (γ x)).comp (fderiv 𝕜 γ x))) (x, 0) :=
  hasFDerivAt_normalExtension_zero (hγ.differentiableAt one_ne_zero).hasFDerivAt
    ((hJ.comp hγ.continuousAt).clm_comp (hγ.continuousAt_fderiv one_ne_zero))

/-- Along the zero section, the tangential derivatives are `Dγ` and the normal derivatives
are `J ∘ Dγ`. -/
theorem fderiv_adaptedNormalExtension_zero {γ : V → W} {J : W → W →L[𝕜] W} {x : V}
    (hγ : ContDiffAt 𝕜 1 γ x) (hJ : ContinuousAt J (γ x)) :
    fderiv 𝕜 (adaptedNormalExtension γ J) (x, 0) =
      (fderiv 𝕜 γ x).coprod ((J (γ x)).comp (fderiv 𝕜 γ x)) :=
  (hasFDerivAt_adaptedNormalExtension_zero hγ hJ).fderiv

/-- The adapted derivative intertwines the standard product structure with the ambient
almost complex structure. Only its square identity at the base point is needed. -/
theorem fderiv_adaptedNormalExtension_intertwines {γ : V → W} {J : W → W →L[𝕜] W} {x : V}
    (hγ : ContDiffAt 𝕜 1 γ x) (hJ : ContinuousAt J (γ x))
    (hsq : ∀ v, J (γ x) (J (γ x) v) = -v) (v w : V) :
    fderiv 𝕜 (adaptedNormalExtension γ J) (x, 0) (-w, v) =
      J (γ x) (fderiv 𝕜 (adaptedNormalExtension γ J) (x, 0) (v, w)) := by
  rw [fderiv_adaptedNormalExtension_zero hγ hJ]
  simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.comp_apply, map_neg,
    map_add, hsq]
  abel

/-- For a linear parametrization, the extension evaluates without a derivative operator. -/
theorem _root_.ContinuousLinearMap.adaptedNormalExtension_apply (L : V →L[𝕜] W)
    (J : W → W →L[𝕜] W) (p : V × V) :
    adaptedNormalExtension L J p = L p.1 + J (L p.1) (L p.2) := by
  simp [adaptedNormalExtension, normalExtension, ContinuousLinearMap.fderiv]

/-- The standard real locus in a product has the identity as its adapted extension. -/
@[simp]
theorem adaptedNormalExtension_inl :
    adaptedNormalExtension (ContinuousLinearMap.inl 𝕜 V V)
      (fun _ ↦ (-ContinuousLinearMap.snd 𝕜 V V).prod (ContinuousLinearMap.fst 𝕜 V V)) = id := by
  funext p
  rw [ContinuousLinearMap.adaptedNormalExtension_apply]
  ext <;> simp

/-- The extension depends on the structure only along the parametrized submanifold. -/
theorem adaptedNormalExtension_congr {γ : V → W} {J K : W → W →L[𝕜] W}
    (h : ∀ x, J (γ x) = K (γ x)) :
    adaptedNormalExtension γ J = adaptedNormalExtension γ K := by
  funext p
  simp only [adaptedNormalExtension, normalExtension, h]

omit [NormedAddCommGroup V] [NormedSpace 𝕜 V] in
/-- Changing the normal frame changes the extension by its action on the normal coordinate. -/
theorem normalExtension_sub_normalExtension (γ : V → W) (A B : V → E →L[𝕜] W) (p : V × E) :
    normalExtension γ A p - normalExtension γ B p = (A p.1 - B p.1) p.2 := by
  simp [normalExtension]

/-- Perturbations of the ambient structure are amplified only by the tangential derivative
and the size of the normal coordinate. -/
theorem norm_adaptedNormalExtension_sub_le (γ : V → W) (J K : W → W →L[𝕜] W)
    (p : V × V) :
    ‖adaptedNormalExtension γ J p - adaptedNormalExtension γ K p‖ ≤
      ‖J (γ p.1) - K (γ p.1)‖ * ‖fderiv 𝕜 γ p.1‖ * ‖p.2‖ := by
  rw [adaptedNormalExtension_eq_normalExtension, adaptedNormalExtension_eq_normalExtension,
    normalExtension_sub_normalExtension, ← ContinuousLinearMap.sub_comp]
  exact ContinuousLinearMap.le_of_opNorm_le _ (ContinuousLinearMap.opNorm_comp_le _ _) _

/-- The first jet is Lipschitz in the value of the ambient structure along the submanifold.
This is a quantitative comparison of actual derivatives, with no derivative assumption on `J`. -/
theorem norm_fderiv_adaptedNormalExtension_sub_le {γ : V → W}
    {J K : W → W →L[𝕜] W} {x : V} (hγ : ContDiffAt 𝕜 1 γ x)
    (hJ : ContinuousAt J (γ x)) (hK : ContinuousAt K (γ x)) :
    ‖fderiv 𝕜 (adaptedNormalExtension γ J) (x, 0) -
        fderiv 𝕜 (adaptedNormalExtension γ K) (x, 0)‖ ≤
      ‖J (γ x) - K (γ x)‖ * ‖fderiv 𝕜 γ x‖ := by
  rw [fderiv_adaptedNormalExtension_zero hγ hJ,
    fderiv_adaptedNormalExtension_zero hγ hK]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro p
  simp only [sub_apply, ContinuousLinearMap.coprod_apply, add_sub_add_left_eq_sub]
  rw [← sub_apply, ← ContinuousLinearMap.sub_comp]
  exact (ContinuousLinearMap.le_of_opNorm_le _
    (ContinuousLinearMap.opNorm_comp_le _ _) _).trans
      (mul_le_mul_of_nonneg_left (norm_snd_le p)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)))

section Family

open Set Filter

variable {ι : Type*} {l : Filter ι} {J : ι → W → W →L[𝕜] W} {J₀ : W → W →L[𝕜] W} {γ : V → W}
  {U : Set V} {Ω : Set W} {ℓ : ℕ}

/-- **The adapted extensions converge in `C^ℓ`.** Let `γ` be `C^(ℓ+1)` on an open `U`, mapping
it into an open `Ω` on which `J₀` and eventually all `J i` are `C^ℓ`. If `J i → J₀` in `C^ℓ` at
`γ x` for some `x ∈ U`, then the adapted extensions `adaptedNormalExtension γ (J i)` converge in
`C^ℓ` to `adaptedNormalExtension γ J₀` at every point `(x, y)`. -/
theorem tendstoContDiffAt_adaptedNormalExtension (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hγ : ContDiffOn 𝕜 (ℓ + 1) γ U) (hγΩ : MapsTo γ U Ω)
    (hJ : ∀ᶠ i in l, ContDiffOn 𝕜 ℓ (J i) Ω) (hJ₀ : ContDiffOn 𝕜 ℓ J₀ Ω) {p : V × V}
    (hp : p.1 ∈ U) (hconv : TendstoContDiffAt 𝕜 ℓ J J₀ l (γ p.1)) :
    TendstoContDiffAt 𝕜 ℓ (fun i ↦ adaptedNormalExtension γ (J i))
      (adaptedNormalExtension γ J₀) l p := by
  -- Write the extension as a fixed smooth map of `(J (γ q.1), (Dγ q.1 q.2, γ q.1))`.
  let G : (W →L[𝕜] W) × (W × W) → W := fun x ↦ x.2.2 + x.1 x.2.1
  let H : V × V → W × W := fun q ↦ (fderiv 𝕜 γ q.1 q.2, γ q.1)
  have hfun (K : W → W →L[𝕜] W) :
      adaptedNormalExtension γ K = G ∘ fun q : V × V ↦ (K (γ q.1), H q) := by
    funext q
    simp [G, H, adaptedNormalExtension_apply]
  have hG : ContDiff 𝕜 ℓ G := by fun_prop
  have hUo : IsOpen (U ×ˢ (univ : Set V)) := hU.prod isOpen_univ
  have hpU : p ∈ U ×ˢ (univ : Set V) := ⟨hp, mem_univ _⟩
  have hfst : MapsTo (Prod.fst : V × V → V) (U ×ˢ univ) U := fun _ hq ↦ hq.1
  have hγℓ : ContDiffOn 𝕜 ℓ γ U := hγ.of_le le_self_add
  have hγf : ContDiffOn 𝕜 ℓ (fun q : V × V ↦ γ q.1) (U ×ˢ univ) := hγℓ.comp contDiffOn_fst hfst
  have hH : ContDiffOn 𝕜 ℓ H (U ×ˢ univ) :=
    (((hγ.fderiv_of_isOpen hU le_rfl).comp contDiffOn_fst hfst).clm_apply contDiffOn_snd).prodMk
      hγf
  -- Eventual regularity near `p`, uniformly along `l`.
  have hnear : ∀ᶠ q in l ×ˢ 𝓝 p, q.2 ∈ U ×ˢ univ := tendsto_snd.eventually (hUo.mem_nhds hpU)
  have hJq : ∀ᶠ q in l ×ˢ 𝓝 p, ContDiffAt 𝕜 ℓ (J q.1) (γ q.2.1) := by
    filter_upwards [tendsto_fst.eventually hJ, hnear] with q hq hqU
    exact hq.contDiffAt (hΩ.mem_nhds (hγΩ hqU.1))
  have hγq : ∀ᶠ q in l ×ˢ 𝓝 p, ContDiffAt 𝕜 ℓ (fun q : V × V ↦ γ q.1) q.2 := by
    filter_upwards [hnear] with q hqU
    exact hγf.contDiffAt (hUo.mem_nhds hqU)
  have hγp : ContDiffAt 𝕜 ℓ (fun q : V × V ↦ γ q.1) p := hγf.contDiffAt (hUo.mem_nhds hpU)
  have hJp : ContDiffAt 𝕜 ℓ J₀ (γ p.1) := hJ₀.contDiffAt (hΩ.mem_nhds (hγΩ hp))
  have h₁ : TendstoContDiffAt 𝕜 ℓ (fun i ↦ J i ∘ fun q : V × V ↦ γ q.1)
      (J₀ ∘ fun q : V × V ↦ γ q.1) l p :=
    TendstoContDiffAt.comp (f := fun _ q ↦ γ q.1) (f₀ := fun q ↦ γ q.1) (x₀ := p) hconv
      hγp.tendstoContDiffAt_const hJq hγq hJp hγp
  have h₂ := h₁.prodMk (g := fun _ ↦ H) (hH.contDiffAt (hUo.mem_nhds hpU)).tendstoContDiffAt_const
    (by filter_upwards [hJq, hγq] with q h1 h2 using h1.comp q.2 h2)
    (by filter_upwards [hnear] with q hqU using hH.contDiffAt (hUo.mem_nhds hqU))
    (hJp.comp p hγp) (hH.contDiffAt (hUo.mem_nhds hpU))
  have h₃ := hG.contDiffAt.tendstoContDiffAt_const.comp h₂
    (Eventually.of_forall fun _ ↦ hG.contDiffAt) (by
      filter_upwards [hJq, hγq, hnear] with q h1 h2 hqU
      exact (h1.comp q.2 h2).prodMk (hH.contDiffAt (hUo.mem_nhds hqU)))
    hG.contDiffAt ((hJp.comp p hγp).prodMk (hH.contDiffAt (hUo.mem_nhds hpU)))
  simp only [hfun]
  exact h₃

end Family

end TauCeti
