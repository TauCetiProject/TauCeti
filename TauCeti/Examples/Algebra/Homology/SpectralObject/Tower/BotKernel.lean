/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.Algebra.Homology.SpectralObject.NatRecipeNeedsClass
public import TauCeti.Algebra.Homology.SpectralObject.Tower.FirstPage
import Mathlib.Algebra.Homology.HomologySequence
import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# The kernel of `δ` into `H^{n+1}(⊥ ≤ q)` can be smaller than every cycle subobject

For a spectral object `X` indexed by `EInt` and the recipe `coreE₂Cohomological`, replacing the
target `H^{n+1}(q - r + 2 ≤ q)` of the `δ` cutting out `Z_r(p, q)` by `H^{n+1}(⊥ ≤ q)` gives a
subobject of `E_2^{p,q}` contained in every `Z_r`
(`SpectralObject.kernelSubobject_δ_le_cyclesSubobject_spectralSequence`). This file shows that
the containment can be strict for every `r` at once, so that this subobject is in general smaller
than the permanent cycles.

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
theorem filtration_one : filtration 1 = Subobject.mk (𝟙 idComplex) := by
  simp [filtration, Subobject.top_eq_id]

/-- `H^n(K) = 0` for `K = (ℤ →(id) ℤ)`, which is contractible. -/
theorem isZero_homology_filtrationFunctor_one (n : ℤ) :
    IsZero ((filtrationFunctor.obj ((1 : ℤ) : EInt)).homology n) :=
  ((exactAt_iff_isZero_homology _ _).1
    ((mappingCone.homotopyToZeroOfId degreeOne).acyclic n)).of_iso
      (homologyMapIso (filtrationFunctorObjIsoOfEqMk _ _ _ filtration_one) n)

/-- **`H^n(i ≤ 0) = 0` for every integer `i ≤ 0`**: it is the homology of `G_0 / G_i = 0`. -/
theorem isZero_H_of_le_zero {i : ℤ} (hi : i ≤ 0) (n : ℤ) :
    IsZero ((spectralObject.H n).obj (mk₁ (eIntHomOfLE hi))) := by
  have : IsIso (filtrationFunctor.map (eIntHomOfLE hi)) := by
    have h : filtrationEInt filtration (i : EInt) = filtrationEInt filtration ((0 : ℤ) : EInt) := by
      rw [filtrationEInt_coe, filtrationEInt_coe, filtration_of_le_zero hi,
        filtration_of_le_zero le_rfl]
    have := (Subobject.isoOfEq _ _ h).isIso_hom
    have : IsIso (filtrationFunctor.map (eIntHomOfLE hi) ≫
        (filtrationFunctorObjIso filtration monotone_filtration _).hom) := by
      rw [filtrationFunctor_map_comp_objIso_hom]
      exact IsIso.comp_isIso' inferInstance this
    exact IsIso.of_isIso_comp_right _ (filtrationFunctorObjIso filtration monotone_filtration _).hom
  exact ((acyclic_of_isZero _ (isZero_cokernel_of_epi _) n).isZero_homology).of_iso
    (spectralObjectHIsoCokernel filtrationFunctor _ n)

/-- **`H^0(⊥ ≤ 1) = 0`**: it is `H^0(G_1) = H^0(K)`. -/
theorem isZero_H_bot_one :
    IsZero ((spectralObject.H 0).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((1 : ℤ) : EInt))))) := by
  have hS := TauCeti.cokernelSequence_shortExact
    (filtrationFunctor.map (homOfLE (bot_le : (⊥ : EInt) ≤ ((1 : ℤ) : EInt))))
  have hbot : IsZero ((filtrationFunctor.obj ⊥).homology 1) :=
    (acyclic_of_isZero _ (isZero_filtrationFunctor_obj_bot _ _) 1).isZero_homology
  refine IsZero.of_iso ?_ (spectralObjectHIsoCokernel filtrationFunctor _ 0)
  exact (hS.homology_exact₃ 0 1 (by simp)).isZero_X₂
    ((isZero_homology_filtrationFunctor_one 0).eq_of_src _ _) (hbot.eq_of_tgt _ _)

/-- **`H^0(0 ≤ 1) ≠ 0`**: it is `H^0(K/K^1) = ℤ`. If it vanished, `H^1(K^1) = ℤ` would inject
into `H^1(K) = 0`. -/
theorem not_isZero_H_zero_one :
    ¬ IsZero ((spectralObject.H 0).obj (mk₁ (eIntHomOfLE (zero_le_one : (0 : ℤ) ≤ 1)))) :=
  fun h => by
  set f := eIntHomOfLE (zero_le_one : (0 : ℤ) ≤ 1)
  have hS := TauCeti.cokernelSequence_shortExact (filtrationFunctor.map f)
  have hQ : IsZero ((cokernel (filtrationFunctor.map f)).homology 0) :=
    h.of_iso (spectralObjectHIsoCokernel filtrationFunctor f 0).symm
  have : Mono (homologyMap (filtrationFunctor.map f) 1) :=
    (hS.homology_exact₁ 0 1 (by simp)).mono_g (hQ.eq_of_src _ _)
  exact not_isZero_homology_degreeOne ((IsZero.of_mono (homologyMap
    (filtrationFunctor.map f) 1) (isZero_homology_filtrationFunctor_one 1)).of_iso
      (homologyMapIso (filtrationFunctorObjIsoOfEqMk _ _ _ (filtration_of_le_zero le_rfl)) 1).symm)

/-- **`δ : H^0(0 ≤ 1) ⟶ H^1(⊥ ≤ 0)` is a monomorphism**, by exactness of
`H^0(⊥ ≤ 1) ⟶ H^0(0 ≤ 1) ⟶ H^1(⊥ ≤ 0)` and `H^0(⊥ ≤ 1) = 0`. The target degree is written
`0 + 1`, the form of `kernelSubobject_δ_le_cyclesSubobject_spectralSequence`. -/
theorem mono_δ_bot :
    Mono (spectralObject.δ (homOfLE (bot_le : (⊥ : EInt) ≤ ((0 : ℤ) : EInt)))
      (eIntHomOfLE (zero_le_one : (0 : ℤ) ≤ 1)) 0 (0 + 1)) :=
  (spectralObject.exact₃ _ _ (homOfLE bot_le) (Subsingleton.elim _ _) 0 (0 + 1)).mono_g
    (isZero_H_bot_one.eq_of_src _ _)

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
    ((0 : ℤ) : EInt) ((1 : ℤ) : EInt) (by simp; lia) rfl rfl 0 rfl]
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
