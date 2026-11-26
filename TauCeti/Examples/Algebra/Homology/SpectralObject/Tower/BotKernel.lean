/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.Algebra.Homology.SpectralObject.NatRecipeNeedsClass
public import TauCeti.Algebra.Homology.SpectralObject.Tower.FirstPage
import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Stabilization

/-!
# The kernel of `δ` into `H^{n+1}(⊥ ≤ q)` can be smaller than every cycle subobject

For a spectral object `X` indexed by `EInt` and the recipe `coreE₂Cohomological`, replacing the
target `H^{n+1}(q - r + 2 ≤ q)` of the `δ` cutting out `Z_r(p, q)` by `H^{n+1}(⊥ ≤ q)` gives a
subobject of `E_2^{p,q}` contained in every `Z_r`
(`SpectralObject.kernelSubobject_δ_le_cyclesSubobject_spectralSequence`). This file shows that
the containment can be strict for every `r` at once: the subobject is strictly smaller than every
`Z_r(0, 0)`. Informally, since every `Z_r(0, 0)` is `⊤` here, it is then also strictly smaller
than the permanent cycles at `(0, 0)`; this file does not state the comparison with `Z_∞`.

Let `K = (ℤ →(id) ℤ)` in degrees `0, 1`
(`TauCeti.Examples.NatRecipeNeedsClass.idComplex`), with the increasing filtration `G_t = K^1`
for `t ≤ 0` and `G_t = K` for `t ≥ 1`. The functor of a filtration
(`CochainComplex.filtrationFunctor`) puts the zero subcomplex at `⊥`, so the filtration is not
separated: `G_t = K^1 ≠ 0` for every integer `t ≤ 0`. At the position `(0, 0)`:

* `Z_r(0, 0) = ⊤` for every `r ≥ 2`: the target `H^1(2 - r ≤ 0) = H^1(G_0 / G_{2-r})` of `δ`
  vanishes, because `G_{2-r} = G_0`;
* the kernel of `δ : H^0(0 ≤ 1) ⟶ H^1(⊥ ≤ 0)` is `⊥`: by the exact sequence
  `H^0(⊥ ≤ 1) ⟶ H^0(0 ≤ 1) ⟶ H^1(⊥ ≤ 0)` of the spectral object, `δ` is a monomorphism because
  `H^0(⊥ ≤ 1) = H^0(K)` vanishes, `K` being contractible;
* `E_2^{0,0} = H^0(0 ≤ 1) = H^0(K/K^1) = ℤ` is nonzero, so `⊥ < ⊤`.

## Main declarations

* `TauCeti.Examples.BotKernel.filtrationFunctor`: the functor `EInt ⥤ CochainComplex` of the
  filtration `G_t = K^1` for `t ≤ 0`, `G_t = K` for `t ≥ 1`.
* `TauCeti.Examples.BotKernel.cyclesSubobject_eq_top`: `Z_r(0, 0) = ⊤` for every `r ≥ 2`.
* `TauCeti.Examples.BotKernel.kernelSubobject_δ_bot_eq_bot`: the kernel of `δ` into
  `H^1(⊥ ≤ 0)` is `⊥`.
* `TauCeti.Examples.BotKernel.kernelSubobject_δ_bot_lt_cyclesSubobject`: it is strictly smaller
  than `Z_r(0, 0)` for every `r ≥ 2`.
-/

public section

noncomputable section

namespace TauCeti.Examples.BotKernel

open CategoryTheory Limits ComposableArrows CategoryTheory.Abelian CochainComplex
  HomologicalComplex NatRecipeNeedsClass

/-- The filtration `G_t = K^1` for `t ≤ 0` and `G_t = K` for `t ≥ 1` of `K = (ℤ →(id) ℤ)`. -/
def filtration (t : ℤ) : Subobject idComplex :=
  if t ≤ 0 then Subobject.mk (mappingCone.inr (𝟙 degreeOne)) else ⊤

/-- The filtration `K^1 ⊆ K` is increasing. -/
theorem monotone_filtration : Monotone filtration := by
  intro s t hst
  unfold filtration
  split_ifs <;> first | exact le_top | exact le_rfl | lia

/-- The functor `EInt ⥤ CochainComplex` of the filtration `K^1 ⊆ K`, with the zero subcomplex at
`⊥`. -/
abbrev filtrationFunctor : EInt ⥤ CochainComplex (ModuleCat ℤ) ℤ :=
  CochainComplex.filtrationFunctor filtration monotone_filtration

/-- The spectral object of the filtration `K^1 ⊆ K`. -/
abbrev spectralObject : SpectralObject (ModuleCat ℤ) EInt :=
  CochainComplex.spectralObject filtrationFunctor

/-- The piece `G_t` for `t ≤ 0` is the degree-`1` term `K^1`. -/
theorem filtration_of_le_zero {t : ℤ} (ht : t ≤ 0) :
    filtration t = Subobject.mk (mappingCone.inr (𝟙 degreeOne)) := by
  simp [filtration, ht]

/-- The piece `G_1` is `K`. -/
theorem filtration_one : filtration 1 = ⊤ := by
  simp [filtration]

/-- **`H^n(i ≤ 0) = 0` for every integer `i ≤ 0`**: it is the homology of `G_0 / G_i = 0`. -/
theorem isZero_H_of_le_zero {i : ℤ} (hi : i ≤ 0) (n : ℤ) :
    IsZero ((spectralObject.H n).obj (mk₁ (eIntHomOfLE hi))) := by
  have := isIso_filtrationFunctor_map_of_eq filtration monotone_filtration (eIntHomOfLE hi)
    (by rw [filtrationEInt_coe, filtrationEInt_coe, filtration_of_le_zero hi,
      filtration_of_le_zero le_rfl])
  exact ((acyclic_of_isZero _ (isZero_cokernel_of_epi _) n).isZero_homology).of_iso
    (spectralObjectHIsoCokernel filtrationFunctor _ n)

/-- **`H^0(0 ≤ 1) ≠ 0`**: it is `H^0(K/K^1) = ℤ`. -/
theorem not_isZero_H_zero_one :
    ¬ IsZero ((spectralObject.H 0).obj (mk₁ (eIntHomOfLE (zero_le_one : (0 : ℤ) ≤ 1)))) :=
  not_isZero_H_zero_of_eq monotone_filtration zero_le_one (filtration_of_le_zero le_rfl)
    filtration_one

/-- **`δ : H^0(0 ≤ 1) ⟶ H^1(⊥ ≤ 0)` is a monomorphism.** The target degree is written `0 + 1`, the
form of `kernelSubobject_δ_le_cyclesSubobject_spectralSequence`. -/
theorem mono_δ_bot :
    Mono (spectralObject.δ (homOfLE (bot_le : (⊥ : EInt) ≤ ((0 : ℤ) : EInt)))
      (eIntHomOfLE (zero_le_one : (0 : ℤ) ≤ 1)) 0 (0 + 1)) :=
  -- In the exact sequence `H^0(⊥ ≤ 1) ⟶ H^0(0 ≤ 1) ⟶ H^1(⊥ ≤ 0)`, the first term is
  -- `H^0(G_1) = H^0(K) = 0`.
  (spectralObject.exact₃ _ _ (homOfLE bot_le) (Subsingleton.elim _ _) 0 (0 + 1)).mono_g
    ((isZero_spectralObject_H_bot filtration monotone_filtration 1 0 (by
      rw [← filtrationFunctor_obj_coe filtration monotone_filtration]
      exact isZero_homology_filtrationFunctor_obj_of_eq_top _ filtration_one 0)).eq_of_src _ _)

/-- The first-page identification `E_2^{0,0} ≅ H^0(0 ≤ 1)`. -/
abbrev firstPageXIso :=
  spectralObject.spectralSequenceFirstPageXIso SpectralObject.coreE₂Cohomological
    ((0 : ℤ), (0 : ℤ)) ((0 : ℤ) : EInt) ((1 : ℤ) : EInt) rfl rfl 0 rfl

/-- **`Z_r(0, 0) = ⊤` for every `r ≥ 2`**: the target `H^1(2 - r ≤ 0)` of the `δ` cutting out
`Z_r` vanishes. -/
theorem cyclesSubobject_eq_top (r : ℤ) (hr : 2 ≤ r) :
    (spectralObject.spectralSequence SpectralObject.coreE₂Cohomological).cyclesSubobject
      ((0 : ℤ), (0 : ℤ)) r hr = ⊤ := by
  rw [spectralObject.cyclesSubobject_spectralSequence_eq_kernelSubobject_δ
    SpectralObject.coreE₂Cohomological ((0 : ℤ), (0 : ℤ)) r hr ((2 - r : ℤ) : EInt)
    ((0 : ℤ) : EInt) ((1 : ℤ) : EInt) (congrArg _ (by lia : 2 - r = 0 - r + 2)) rfl rfl 0 rfl]
  convert kernelSubobject_zero using 2
  exact (isZero_H_of_le_zero (by lia : 2 - r ≤ 0) (0 + 1)).eq_of_tgt _ _

/-- **The kernel of `δ : E_2^{0,0} ⟶ H^1(⊥ ≤ 0)` is `⊥`**, `δ` being a monomorphism. -/
theorem kernelSubobject_δ_bot_eq_bot :
    kernelSubobject (firstPageXIso.hom ≫
      spectralObject.δ (homOfLE (bot_le : (⊥ : EInt) ≤ ((0 : ℤ) : EInt)))
        (eIntHomOfLE (zero_le_one : (0 : ℤ) ≤ 1)) 0 (0 + 1)) = ⊥ := by
  have := mono_δ_bot
  rw [kernelSubobject, Subobject.mk_eq_bot_iff_zero]
  exact kernel.ι_of_mono _

/-- **The kernel of `δ` into `H^1(⊥ ≤ 0)` is strictly smaller than every `Z_r(0, 0)`**: it is
`⊥`, every `Z_r(0, 0)` is `⊤`, and `E_2^{0,0} = H^0(0 ≤ 1)` is nonzero. -/
theorem kernelSubobject_δ_bot_lt_cyclesSubobject (r : ℤ) (hr : 2 ≤ r) :
    kernelSubobject (firstPageXIso.hom ≫
      spectralObject.δ (homOfLE (bot_le : (⊥ : EInt) ≤ ((0 : ℤ) : EInt)))
        (eIntHomOfLE (zero_le_one : (0 : ℤ) ≤ 1)) 0 (0 + 1)) <
      (spectralObject.spectralSequence SpectralObject.coreE₂Cohomological).cyclesSubobject
        ((0 : ℤ), (0 : ℤ)) r hr := by
  have := Subobject.nontrivial_of_not_isZero
    (fun h => not_isZero_H_zero_one (h.of_iso firstPageXIso.symm))
  rw [kernelSubobject_δ_bot_eq_bot, cyclesSubobject_eq_top r hr]
  exact bot_lt_top

end TauCeti.Examples.BotKernel
