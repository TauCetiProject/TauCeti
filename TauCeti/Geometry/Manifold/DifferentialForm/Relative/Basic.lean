/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.HomotopyOperator
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.VectorBundle.FiberScaling

/-!
# The relative Poincaré lemma on the total space of a vector bundle

Let `V → B` be a smooth real vector bundle. Fibre scaling
`H : V × [0, 1] → V`, `(v, t) ↦ t • v` (`TauCeti.vectorBundleFiberScaling`), is a smooth homotopy
from the retraction `ρ = 0 ∘ π` of `V` onto its zero section to the identity, and it fixes the
zero section at all times. Applying the homotopy operator of the cylinder `V × [0, 1]` to `H^* η`
gives the *relative Poincaré operator* `P` (`TauCeti.vectorBundlePoincareHomotopy`)

`β = P η = h (H^* η)`, `β(v)(w₁, …, wₖ) = ∫₀¹ η(t • v)(dH ∂ₜ, dH w₁, …, dH wₖ) dt`.

Since `H` is constant in time along the zero section, `dH ∂ₜ = 0` there, so `β` vanishes at
every point of the zero section as a full ambient tensor, for every form `η`
(`TauCeti.vectorBundlePoincareHomotopy_zeroSection`), even when `η` does not. For a `C¹` form `η`
of positive degree, the cochain-homotopy identity of the homotopy operator gives

`d (P η) + P (d η) = η - ρ^* η`

(`TauCeti.mextDeriv_vectorBundlePoincareHomotopy_add_vectorBundlePoincareHomotopy_mextDeriv`), so
`d β = η - ρ^* η` when `η` is closed (`TauCeti.mextDeriv_vectorBundlePoincareHomotopy`), and
`ρ^* η = π^* (i^* η)` only depends on the restriction `i^* η` of `η` to the zero section `i`
(`TauCeti.mpullback_zeroSection_comp_proj`). Hence `d β = η` as soon as `i^* η = 0`
(`TauCeti.mextDeriv_vectorBundlePoincareHomotopy_of_mpullback_zeroSection_eq_zero`), although `η`
need not vanish as a full ambient tensor along the zero section. The operator preserves `C^r`
regularity over a `C^(r + 1)` bundle (`TauCeti.IsSmoothForm.vectorBundlePoincareHomotopy`) and is
additive on continuous forms (`TauCeti.vectorBundlePoincareHomotopy_add`). The identities above
need only a `C²` bundle.

Everything transports along a diffeomorphism `Φ` from the total space onto a manifold `M`, such as
a tubular neighbourhood of an embedded submanifold
(`TauCeti.SmoothEmbedding.exists_isSmoothForm_relative_primitive`). With the zero-section inclusion
`i = Φ ∘ 0` and the retraction `ρ = Φ ∘ 0 ∘ π ∘ Φ⁻¹`, every closed `C^r` form `η` of positive
degree on `M`, with `r ≥ 1`, has a `C^r` form `β` with `d β = η - ρ^* η` that vanishes along
`i` as a full ambient tensor (`Diffeomorph.exists_isSmoothForm_mextDeriv_eq_sub_mpullback`), and
`d β = η` when `i^* η = 0` (`Diffeomorph.exists_isSmoothForm_relative_primitive`). This needs `Φ`
and the bundle to be `C^(r + 1)`. This is the primitive used to compare two symplectic forms
relative to a submanifold.

The flat counterpart on an open set stable under scaling the normal coordinate is
`IsOpen.exists_contDiffOn_relative_primitive`. The base may have boundary or corners and the
coefficient space is any Banach space.

## Main declarations

* `TauCeti.vectorBundlePoincareHomotopy`: the relative Poincaré operator `β = h (H^* η)`.
* `TauCeti.vectorBundlePoincareHomotopy_zeroSection`: `β` vanishes along the zero section.
* `TauCeti.mextDeriv_vectorBundlePoincareHomotopy_add_vectorBundlePoincareHomotopy_mextDeriv`:
  `d (P η) + P (d η) = η - ρ^* η`.
* `TauCeti.mextDeriv_vectorBundlePoincareHomotopy`: `d β = η - ρ^* η` for closed `η`.
* `Diffeomorph.mextDeriv_mpullback_symm_vectorBundlePoincareHomotopy`,
  `Diffeomorph.mextDeriv_mpullback_symm_vectorBundlePoincareHomotopy_of_eq_zero`: the
  transported primitive `(Φ⁻¹)^* P (Φ^* η)` satisfies `d β = η - ρ^* η`, and `d β = η` when
  `i^* η = 0`; it is `C^r` for `C^r` data
  (`Diffeomorph.isSmoothForm_mpullback_symm_vectorBundlePoincareHomotopy`) and vanishes along the
  core (`Diffeomorph.mpullback_symm_vectorBundlePoincareHomotopy_zeroSection`).
* `Diffeomorph.exists_isSmoothForm_relative_primitive`: the relative Poincaré lemma on a tube.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, §6.2 (the relative Poincaré lemma by fibre scaling).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §4.
-/

public section

noncomputable section

open Set Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {B FV : Type*} {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)]

variable {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup FV] [NormedSpace ℝ FV]
  [∀ b, TopologicalSpace (V b)] [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-! ### The relative Poincaré operator -/

/-- The **relative Poincaré operator** of a vector bundle: the homotopy operator of the cylinder
`V × [0, 1]` applied to the pullback of `η` by fibre scaling `H(v, t) = t • v`,

`β(v)(w₁, …, wₖ) = ∫₀¹ η(t • v)(dH ∂ₜ, dH (w₁, 0), …, dH (wₖ, 0)) dt`.

It vanishes along the zero section (`TauCeti.vectorBundlePoincareHomotopy_zeroSection`), and for a
closed `C¹` form `η`, `d β = η - ρ^* η` with `ρ` the retraction onto the zero section
(`TauCeti.mextDeriv_vectorBundlePoincareHomotopy`). -/
def vectorBundlePoincareHomotopy
    (η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)) :
    RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F k :=
  homotopyOperator
    (mpullback ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, FV))
      (vectorBundleFiberScaling FV V) η)

/-- The relative Poincaré operator is the homotopy operator of the pullback by fibre scaling. -/
theorem vectorBundlePoincareHomotopy_def
    (η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)) :
    vectorBundlePoincareHomotopy η =
      homotopyOperator (mpullback ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, FV))
        (vectorBundleFiberScaling FV V) η) :=
  (rfl)

/-- The relative Poincaré operator of the zero form is zero. -/
@[simp]
theorem vectorBundlePoincareHomotopy_zero :
    vectorBundlePoincareHomotopy
      (0 : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)) = 0 := by
  rw [vectorBundlePoincareHomotopy_def, mpullback_zero, homotopyOperator_zero]

/-- The relative Poincaré operator commutes with real scalar multiplication of forms. -/
@[simp]
theorem vectorBundlePoincareHomotopy_smul (c : ℝ)
    (η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)) :
    vectorBundlePoincareHomotopy (c • η) = c • vectorBundlePoincareHomotopy η := by
  rw [vectorBundlePoincareHomotopy_def, mpullback_smul, homotopyOperator_smul,
    vectorBundlePoincareHomotopy_def]

variable [VectorBundle ℝ FV V]

/-- **The relative Poincaré operator vanishes along the zero section**, as a full ambient tensor,
for every form `η`: fibre scaling kills the time direction there. -/
@[simp]
theorem vectorBundlePoincareHomotopy_zeroSection
    (η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)) (b : B) :
    vectorBundlePoincareHomotopy η (zeroSection FV V b) = 0 :=
  homotopyOperator_apply_eq_zero fun t _ ↦ by
    rw [mpullback_apply]
    exact (η _).map_coord_zero 0 (mfderiv_vectorBundleFiberScaling_zeroSection_time b t _)

/-- The relative Poincaré operator is additive on continuous forms, over a `C¹` vector bundle on a
`C¹` base. -/
theorem vectorBundlePoincareHomotopy_add [IsManifold IB 1 B] [ContMDiffVectorBundle 1 FV V IB]
    {η₁ η₂ : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (h₁ : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 0 η₁) (h₂ : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 0 η₂) :
    vectorBundlePoincareHomotopy (η₁ + η₂) =
      vectorBundlePoincareHomotopy η₁ + vectorBundlePoincareHomotopy η₂ := by
  rw [vectorBundlePoincareHomotopy_def, mpullback_add,
    homotopyOperator_add (h₁.mpullback contMDiff_vectorBundleFiberScaling)
      (h₂.mpullback contMDiff_vectorBundleFiberScaling)]
  rfl

/-- The relative Poincaré operator preserves `C^r` regularity of forms, over a `C^(r + 1)` vector
bundle on a `C^(r + 1)` base. -/
theorem IsSmoothForm.vectorBundlePoincareHomotopy {r : ℕ∞} [IsManifold IB 1 B]
    [ContMDiffVectorBundle 1 FV V IB] [IsManifold IB (r + 1) B]
    [ContMDiffVectorBundle (r + 1) FV V IB]
    {η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (hη : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) r η) :
    IsSmoothForm (IB.prod 𝓘(ℝ, FV)) r (vectorBundlePoincareHomotopy η) := by
  exact IsSmoothForm.homotopyOperator (hη.mpullback contMDiff_vectorBundleFiberScaling)

variable [CompleteSpace F]

/-- **The relative cochain-homotopy identity.** For a `C¹` form `η` of positive degree on the total
space of a `C²` vector bundle over a `C²` base, `d β + P (d η) = η - ρ^* η`, where `P` is the
relative Poincaré operator, `β = P η`, and `ρ = 0 ∘ π` is the retraction onto the zero section. -/
theorem mextDeriv_vectorBundlePoincareHomotopy_add_vectorBundlePoincareHomotopy_mextDeriv
    [IsManifold IB 2 B] [ContMDiffVectorBundle 2 FV V IB]
    {η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (hη : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 1 η) :
    mextDeriv (vectorBundlePoincareHomotopy η) + vectorBundlePoincareHomotopy (mextDeriv η) =
      η - mpullback (IB.prod 𝓘(ℝ, FV)) (IB.prod 𝓘(ℝ, FV))
        (zeroSection FV V ∘ TotalSpace.proj) η := by
  have hH : ContMDiff ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, FV)) 2
      (vectorBundleFiberScaling FV V) :=
    contMDiff_vectorBundleFiberScaling
  have hι (s : Icc (0 : ℝ) 1) : MDifferentiable (IB.prod 𝓘(ℝ, FV))
      ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1)) (fun v : TotalSpace FV V ↦ (v, s)) :=
    mdifferentiable_id.prodMk mdifferentiable_const
  have h₁ : vectorBundleFiberScaling FV V ∘ (fun v ↦ (v, 1)) = id :=
    funext fun v ↦ vectorBundleFiberScaling_one v
  have h₀ : vectorBundleFiberScaling FV V ∘ (fun v ↦ (v, 0)) =
      zeroSection FV V ∘ TotalSpace.proj :=
    funext fun v ↦ vectorBundleFiberScaling_zero v
  funext v
  rw [Pi.add_apply, vectorBundlePoincareHomotopy_def, vectorBundlePoincareHomotopy_def,
    mpullback_mextDeriv hH ((isSmoothBundleForm_def 1 _).mpr hη.contMDiff),
    mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv
      (hη.mpullback (hH.of_le (by norm_num))),
    ← mpullback_comp_at (hι 1 v) (hH.mdifferentiable two_ne_zero _),
    ← mpullback_comp_at (hι 0 v) (hH.mdifferentiable two_ne_zero _), h₁, h₀, mpullback_id,
    Pi.sub_apply]

/-- **The relative Poincaré identity.** For a closed `C¹` form `η` of positive degree on the total
space of a `C²` vector bundle over a `C²` base, `d β = η - ρ^* η`, where `β` is the relative
Poincaré operator of `η` and `ρ = 0 ∘ π` is the retraction onto the zero section. -/
theorem mextDeriv_vectorBundlePoincareHomotopy [IsManifold IB 2 B]
    [ContMDiffVectorBundle 2 FV V IB]
    {η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (hη : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 1 η) (hclosed : mextDeriv η = 0) :
    mextDeriv (vectorBundlePoincareHomotopy η) =
      η - mpullback (IB.prod 𝓘(ℝ, FV)) (IB.prod 𝓘(ℝ, FV))
        (zeroSection FV V ∘ TotalSpace.proj) η := by
  rw [← mextDeriv_vectorBundlePoincareHomotopy_add_vectorBundlePoincareHomotopy_mextDeriv hη,
    hclosed, vectorBundlePoincareHomotopy_zero, add_zero]

/-- **The relative Poincaré lemma on the total space of a vector bundle.** If a closed `C¹` form
`η` of positive degree, on the total space of a `C²` vector bundle over a `C²` base, restricts to
zero on the zero section, then the relative Poincaré operator is a primitive of `η`, which
vanishes along the zero section as a full ambient tensor. The form `η` itself need not vanish as
an ambient tensor there. -/
theorem mextDeriv_vectorBundlePoincareHomotopy_of_mpullback_zeroSection_eq_zero
    [IsManifold IB 2 B] [ContMDiffVectorBundle 2 FV V IB]
    {η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (hη : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 1 η) (hclosed : mextDeriv η = 0)
    (hi : mpullback IB (IB.prod 𝓘(ℝ, FV)) (zeroSection FV V) η = 0) :
    mextDeriv (vectorBundlePoincareHomotopy η) = η := by
  rw [mextDeriv_vectorBundlePoincareHomotopy hη hclosed, mpullback_zeroSection_comp_proj, hi,
    mpullback_zero, sub_zero]

/-! ### Transport to a tube -/

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {n : WithTop ℕ∞} [IsManifold IB n B] [ContMDiffVectorBundle n FV V IB]

omit [CompleteSpace F] in
/-- The transported relative Poincaré primitive `(Φ⁻¹)^* P (Φ^* η)` of a `C^r` form `η` along a
`C^n` diffeomorphism `Φ` from the total space of a `C^n` vector bundle, with `r + 1 ≤ n`, is a `C^r`
form. -/
theorem _root_.Diffeomorph.isSmoothForm_mpullback_symm_vectorBundlePoincareHomotopy
    (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M) {r : ℕ∞} (hn : r + 1 ≤ n)
    {η : RoughForm I M F (k + 1)} (hη : IsSmoothForm I r η) :
    IsSmoothForm I r (mpullback I (IB.prod 𝓘(ℝ, FV)) Φ.symm
      (vectorBundlePoincareHomotopy (mpullback (IB.prod 𝓘(ℝ, FV)) I Φ η))) := by
  have : IsManifold IB ((r : WithTop ℕ∞) + 1) B := .of_le hn
  have : ContMDiffVectorBundle ((r : WithTop ℕ∞) + 1) FV V IB := .of_le hn
  have h1 : (1 : WithTop ℕ∞) ≤ n := le_trans (by exact_mod_cast le_add_self) hn
  have : IsManifold IB 1 B := .of_le h1
  have : ContMDiffVectorBundle 1 FV V IB := .of_le h1
  exact (hη.mpullback (Φ.contMDiff.of_le hn)).vectorBundlePoincareHomotopy.mpullback
    (Φ.symm.contMDiff.of_le hn)

omit [CompleteSpace F] [IsManifold I 2 M] [IsManifold IB n B] [ContMDiffVectorBundle n FV V IB] in
/-- The transported relative Poincaré primitive `(Φ⁻¹)^* P (Φ^* η)` vanishes, as a full ambient
tensor, at every point `Φ(0_b)` of the core of the tube. -/
theorem _root_.Diffeomorph.mpullback_symm_vectorBundlePoincareHomotopy_zeroSection
    (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M) (η : RoughForm I M F (k + 1)) (b : B) :
    mpullback I (IB.prod 𝓘(ℝ, FV)) Φ.symm
      (vectorBundlePoincareHomotopy (mpullback (IB.prod 𝓘(ℝ, FV)) I Φ η))
        (Φ (zeroSection FV V b)) = 0 :=
  mpullback_apply_eq_zero ((congrArg _ (Φ.symm_apply_apply _)).trans
    (vectorBundlePoincareHomotopy_zeroSection _ b))

/-- **The transported relative Poincaré primitive.** Let `Φ` be a `C^n` diffeomorphism, `n ≥ 2`,
from the total space of a `C^n` vector bundle onto `M`, with retraction `ρ = Φ ∘ 0 ∘ π ∘ Φ⁻¹` onto
the image of the zero section. For every closed `C¹` form `η` of positive degree on `M`, the form
`β = (Φ⁻¹)^* P (Φ^* η)`, obtained by transporting the relative Poincaré operator `P` along `Φ`,
satisfies `d β = η - ρ^* η`. -/
theorem _root_.Diffeomorph.mextDeriv_mpullback_symm_vectorBundlePoincareHomotopy
    (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M) (hn : 2 ≤ n)
    {η : RoughForm I M F (k + 1)} (hη : IsSmoothForm I 1 η) (hclosed : mextDeriv η = 0) :
    mextDeriv (mpullback I (IB.prod 𝓘(ℝ, FV)) Φ.symm
        (vectorBundlePoincareHomotopy (mpullback (IB.prod 𝓘(ℝ, FV)) I Φ η))) =
      η - mpullback I I (Φ ∘ zeroSection FV V ∘ π FV V ∘ Φ.symm) η := by
  have hn0 : n ≠ 0 := (lt_of_lt_of_le (by norm_num) hn).ne'
  have : IsManifold IB 2 B := .of_le hn
  have : ContMDiffVectorBundle 2 FV V IB := .of_le hn
  have : IsManifold IB (((1 : ℕ∞) : WithTop ℕ∞) + 1) B := .of_le hn
  have : ContMDiffVectorBundle (((1 : ℕ∞) : WithTop ℕ∞) + 1) FV V IB := .of_le hn
  have hη₀ := hη.mpullback (Φ.contMDiff.of_le hn)
  have hβ₀ := hη₀.vectorBundlePoincareHomotopy
  have hd := Φ.mdifferentiable hn0
  have hds := Φ.symm.mdifferentiable hn0
  have hZ := (contMDiff_zeroSection ℝ V (IB := IB) (F := FV) (n := 1)).mdifferentiable one_ne_zero
  have hp := (Bundle.contMDiff_proj (IB := IB) (n := 1) (F := FV) V).mdifferentiable one_ne_zero
  rw [← mpullback_mextDeriv (Φ.symm.contMDiff.of_le hn)
      ((isSmoothBundleForm_def 1 _).mpr hβ₀.contMDiff),
    mextDeriv_vectorBundlePoincareHomotopy hη₀
      (hη.mextDeriv_mpullback_eq_zero hclosed (Φ.contMDiff.of_le hn)),
    mpullback_sub, mpullback_symm_mpullback hn0, ← mpullback_comp (hZ.comp hp) hd,
    ← mpullback_comp hds (hd.comp (hZ.comp hp))]
  -- Both retractions are `Φ ∘ 0 ∘ π ∘ Φ⁻¹`, associated differently.
  simp only [Function.comp_assoc]

/-- **The transported relative Poincaré primitive**, for forms restricting to zero on the core.
Let `Φ` be a `C^n` diffeomorphism, `n ≥ 2`, from the total space of a `C^n` vector bundle onto `M`,
with zero-section inclusion `i = Φ ∘ 0`. For every closed `C¹` form `η` of positive degree on `M`
with `i^* η = 0`, the transported primitive `β = (Φ⁻¹)^* P (Φ^* η)` satisfies `d β = η`: the
retraction `ρ = Φ ∘ 0 ∘ π ∘ Φ⁻¹` factors through `i`, so `ρ^* η = 0`. -/
theorem _root_.Diffeomorph.mextDeriv_mpullback_symm_vectorBundlePoincareHomotopy_of_eq_zero
    (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M) (hn : 2 ≤ n)
    {η : RoughForm I M F (k + 1)} (hη : IsSmoothForm I 1 η) (hclosed : mextDeriv η = 0)
    (hi : mpullback IB I (Φ ∘ zeroSection FV V) η = 0) :
    mextDeriv (mpullback I (IB.prod 𝓘(ℝ, FV)) Φ.symm
        (vectorBundlePoincareHomotopy (mpullback (IB.prod 𝓘(ℝ, FV)) I Φ η))) = η := by
  have hn0 : n ≠ 0 := (lt_of_lt_of_le (by norm_num) hn).ne'
  have : IsManifold IB 1 B := .of_le (le_trans (by norm_num) hn)
  have hp := (Bundle.contMDiff_proj (IB := IB) (n := 1) (F := FV) V).mdifferentiable one_ne_zero
  have hiΦ := (Φ.contMDiff.comp (contMDiff_zeroSection ℝ V (IB := IB) (F := FV))).mdifferentiable
    hn0
  rw [Φ.mextDeriv_mpullback_symm_vectorBundlePoincareHomotopy hn hη hclosed,
    ← Function.comp_assoc (Φ : TotalSpace FV V → M) (zeroSection FV V),
    mpullback_comp (hp.comp (Φ.symm.mdifferentiable hn0)) hiΦ, hi, mpullback_zero, sub_zero]

/-- **The relative Poincaré lemma on a tube.** Let `Φ` be a `C^n` diffeomorphism from the total
space of a `C^n` vector bundle onto `M`, such as a tubular neighbourhood, with zero-section
inclusion `i = Φ ∘ 0` and retraction `ρ = Φ ∘ 0 ∘ π ∘ Φ⁻¹` onto its image. Every closed `C^r`
form `η` of positive degree on `M`, with `1 ≤ r` and `r + 1 ≤ n`, has a `C^r` form `β` with
`d β = η - ρ^* η` that vanishes along `i` as a full ambient tensor. -/
theorem _root_.Diffeomorph.exists_isSmoothForm_mextDeriv_eq_sub_mpullback
    (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M) {r : ℕ∞} (hr : 1 ≤ r) (hn : r + 1 ≤ n)
    {η : RoughForm I M F (k + 1)} (hη : IsSmoothForm I r η) (hclosed : mextDeriv η = 0) :
    ∃ β : RoughForm I M F k, IsSmoothForm I r β ∧
      mextDeriv β = η - mpullback I I (Φ ∘ zeroSection FV V ∘ π FV V ∘ Φ.symm) η ∧
      ∀ b, β (Φ (zeroSection FV V b)) = 0 :=
  ⟨_, Φ.isSmoothForm_mpullback_symm_vectorBundlePoincareHomotopy hn hη,
    Φ.mextDeriv_mpullback_symm_vectorBundlePoincareHomotopy
      (le_trans (by rw [← one_add_one_eq_two]; gcongr; exact_mod_cast hr) hn)
      (hη.of_le (by exact_mod_cast hr)) hclosed,
    Φ.mpullback_symm_vectorBundlePoincareHomotopy_zeroSection η⟩

/-- **The relative Poincaré lemma on a tube**, for forms restricting to zero on the core. Let `Φ`
be a `C^n` diffeomorphism from the total space of a `C^n` vector bundle onto `M`, such as a
tubular neighbourhood, with zero-section inclusion `i = Φ ∘ 0`. Every closed `C^r` form `η` of
positive degree on `M` with `i^* η = 0`, where `1 ≤ r` and `r + 1 ≤ n`, is the exterior
derivative of a `C^r` form `β` that vanishes along `i` as a full ambient tensor. -/
theorem _root_.Diffeomorph.exists_isSmoothForm_relative_primitive
    (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M) {r : ℕ∞} (hr : 1 ≤ r) (hn : r + 1 ≤ n)
    {η : RoughForm I M F (k + 1)} (hη : IsSmoothForm I r η) (hclosed : mextDeriv η = 0)
    (hi : mpullback IB I (Φ ∘ zeroSection FV V) η = 0) :
    ∃ β : RoughForm I M F k, IsSmoothForm I r β ∧ mextDeriv β = η ∧
      ∀ b, β (Φ (zeroSection FV V b)) = 0 :=
  ⟨_, Φ.isSmoothForm_mpullback_symm_vectorBundlePoincareHomotopy hn hη,
    Φ.mextDeriv_mpullback_symm_vectorBundlePoincareHomotopy_of_eq_zero
      (le_trans (by rw [← one_add_one_eq_two]; gcongr; exact_mod_cast hr) hn)
      (hη.of_le (by exact_mod_cast hr)) hclosed hi,
    Φ.mpullback_symm_vectorBundlePoincareHomotopy_zeroSection η⟩

end TauCeti
