/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Double
public import TauCeti.Algebra.Homology.SpectralObject.Tower.FirstPage
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.SpectralObject
import Mathlib.Algebra.Homology.HomologySequence
import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# The cycle tower of the complex `ℤ →(×2) ℤ`

Let `K = (ℤ →(×2) ℤ)` in degrees `0, 1`, with the stupid filtration `F^0 = K`, `F^1 = K^1`,
`F^2 = 0`, read as the increasing filtration `G_t = F^{-t}`: `G_t = 0` for `t ≤ -2`,
`G_{-1} = K^1` and `G_t = K` for `t ≥ 0`. For its spectral object
(`CochainComplex.spectralObject`) and the recipe `coreE₂Cohomological`, at the native position
`(1, -1)` the cycles `Z_3` are the kernel of `δ : H^0(-1 ≤ 0) ⟶ H^1(-2 ≤ -1)` (multiplication by
`2` from `H^0(K/K^1) = ℤ` to `H^1(K^1) = ℤ`), hence `0`.

We do not identify `δ` with multiplication by `2`: it is enough that `δ` is a monomorphism. By
the exact sequence `H^0(-2 ≤ 0) ⟶ H^0(-1 ≤ 0) ⟶ H^1(-2 ≤ -1)` of the spectral object, this
follows from `H^0(-2 ≤ 0) = H^0(K) = 0`, and `H^0(K) = 0` because `×2` is injective on `ℤ`.

## Main declarations

* `TauCeti.Examples.TimesTwo.complex`: the complex `ℤ →(×2) ℤ` in degrees `0, 1`.
* `TauCeti.Examples.TimesTwo.isZero_homology_zero`: `H^0(K) = 0`.
* `TauCeti.Examples.TimesTwo.mono_δ`: `δ : H^0(-1 ≤ 0) ⟶ H^1(-2 ≤ -1)` is a monomorphism.
* `TauCeti.Examples.TimesTwo.cyclesSubobject_three_eq_bot`: `Z_3(1, -1) = 0`.
-/

public section

noncomputable section

namespace TauCeti.Examples.TimesTwo

open CategoryTheory Limits ComposableArrows CategoryTheory.Abelian CochainComplex
  HomologicalComplex

/-- `0 + 1 = 1`: degrees `0` and `1` are related in `ComplexShape.up ℤ`. -/
theorem rel_zero_one : (ComplexShape.up ℤ).Rel 0 1 := by simp

/-- The complex `K = (ℤ →(×2) ℤ)` in degrees `0, 1`. -/
abbrev complex : CochainComplex (ModuleCat ℤ) ℤ :=
  double (2 • 𝟙 (ModuleCat.of ℤ ℤ)) rel_zero_one

/-- The complex `ℤ[-1]`: the abelian group `ℤ` concentrated in degree `1`. -/
abbrev degreeOne : CochainComplex (ModuleCat ℤ) ℤ :=
  (single (ModuleCat ℤ) (ComplexShape.up ℤ) 1).obj (ModuleCat.of ℤ ℤ)

/-- The inclusion of the degree-`1` term `K^1` into `K`, as a morphism of complexes. -/
def inclusion : degreeOne ⟶ complex :=
  mkHomFromSingle (doubleXIso₁ _ rel_zero_one (by simp)).inv (fun k _ => by
    rw [double_d_eq_zero₀ _ _ _ _ (by simp), comp_zero])

/-- The inclusion of `K^1` into `K` is a monomorphism: it is an isomorphism in degree `1`. -/
instance mono_inclusion : Mono inclusion := by
  refine mono_of_mono_f _ fun i => ?_
  by_cases hi : i = 1
  · subst hi
    rw [inclusion, mkHomFromSingle_f]
    infer_instance
  · exact (isZero_single_obj_X _ 1 _ i hi).mono _

/-- The filtration `G_t = 0` for `t ≤ -2`, `G_{-1} = K^1` and `G_t = K` for `t ≥ 0`. -/
def filtration (t : ℤ) : Subobject complex :=
  if t ≤ -2 then ⊥ else if t = -1 then Subobject.mk inclusion else ⊤

/-- The filtration `0 ⊆ K^1 ⊆ K` is increasing. -/
theorem monotone_filtration : Monotone filtration := by
  intro s t hst
  unfold filtration
  split_ifs <;> first | exact bot_le | exact le_top | exact le_rfl | lia

/-- The functor `EInt ⥤ CochainComplex` of the filtration `0 ⊆ K^1 ⊆ K`. -/
abbrev filtrationFunctor : EInt ⥤ CochainComplex (ModuleCat ℤ) ℤ :=
  CochainComplex.filtrationFunctor filtration monotone_filtration

/-- The spectral object of the stupid filtration of `ℤ →(×2) ℤ`. -/
abbrev spectralObject : SpectralObject (ModuleCat ℤ) EInt :=
  CochainComplex.spectralObject filtrationFunctor

/-- **`H^0(K) = 0`** for `K = (ℤ →(×2) ℤ)`: the differential `×2` is injective. -/
theorem isZero_homology_zero : IsZero (complex.homology 0) := by
  rw [← exactAt_iff_isZero_homology, exactAt_iff' complex (-1) 0 1 (by simp) (by simp),
    ShortComplex.exact_iff_mono _ (double_d_eq_zero₀ _ rel_zero_one _ _ (by simp))]
  dsimp
  rw [double_d _ _ (by simp)]
  have : Mono (2 • 𝟙 (ModuleCat.of ℤ ℤ)) := (ModuleCat.mono_iff_injective _).2 fun x y h => by
    simpa using h
  infer_instance

/-- The inequality `a ≤ b` between integers, viewed in `EInt`. -/
theorem coe_le_coe_of_le {a b : ℤ} (h : a ≤ b) : ((a : ℤ) : EInt) ≤ ((b : ℤ) : EInt) :=
  WithBotTop.coe_le_coe.2 h

/-- **`H^0(-2 ≤ 0) = 0`**: it is `H^0(G_0 / G_{-2}) = H^0(K)`. -/
theorem isZero_H_zero : IsZero ((spectralObject.H 0).obj
    (mk₁ (homOfLE (coe_le_coe_of_le (by norm_num : (-2 : ℤ) ≤ 0))))) := by
  set f : ((-2 : ℤ) : EInt) ⟶ ((0 : ℤ) : EInt) := homOfLE (coe_le_coe_of_le (by norm_num))
  have hS := TauCeti.cokernelSequence_shortExact (filtrationFunctor.map f)
  have h0 : filtration 0 = Subobject.mk (𝟙 complex) := by
    simp [filtration, Subobject.top_eq_id]
  have hK : IsZero ((filtrationFunctor.obj ((0 : ℤ) : EInt)).homology 0) :=
    isZero_homology_zero.of_iso (homologyMapIso (filtrationFunctorObjIsoOfEqMk _ _ _ h0) 0)
  have hbot : IsZero (filtrationFunctor.obj ((-2 : ℤ) : EInt)) := by
    have h2 : filtration (-2) = ⊥ := by simp [filtration]
    exact (isZero_zero _).of_iso (filtrationFunctorObjIso _ _ _ ≪≫
      eqToIso (congrArg (fun S : Subobject complex => (S : CochainComplex (ModuleCat ℤ) ℤ))
        ((filtrationEInt_coe _ _).trans h2)) ≪≫ Subobject.botCoeIsoZero)
  refine IsZero.of_iso ?_ (spectralObjectHIsoCokernel filtrationFunctor f 0)
  exact (hS.homology_exact₃ 0 1 (by simp)).isZero_X₂ (hK.eq_of_src _ _)
    ((Functor.map_isZero (homologyFunctor _ _ 1) hbot).eq_of_tgt _ _)

/-- **`δ : H^0(-1 ≤ 0) ⟶ H^1(-2 ≤ -1)` is a monomorphism**, by exactness of
`H^0(-2 ≤ 0) ⟶ H^0(-1 ≤ 0) ⟶ H^1(-2 ≤ -1)` and `H^0(-2 ≤ 0) = 0`. -/
theorem mono_δ :
    Mono (spectralObject.δ (homOfLE (coe_le_coe_of_le (by norm_num : (-2 : ℤ) ≤ -1)))
      (homOfLE (coe_le_coe_of_le (by norm_num : (-1 : ℤ) ≤ 0))) 0 1) :=
  (spectralObject.exact₃ _ _ (homOfLE (coe_le_coe_of_le (by norm_num))) (Subsingleton.elim _ _)
    0 1).mono_g (isZero_H_zero.eq_of_src _ _)

/-- **`Z_3(1, -1) = 0`** for the stupid filtration of `ℤ →(×2) ℤ`: through the first page, the
cycles `Z_3` at the native position `(1, -1)` are the kernel of the monomorphism
`δ : H^0(-1 ≤ 0) ⟶ H^1(-2 ≤ -1)`. -/
theorem cyclesSubobject_three_eq_bot :
    (spectralObject.spectralSequence SpectralObject.coreE₂Cohomological).cyclesSubobject
      ((1 : ℤ), (-1 : ℤ)) 3 (by norm_num) = ⊥ := by
  rw [spectralObject.cyclesSubobject_spectralSequence_eq_kernelSubobject_δ
    SpectralObject.coreE₂Cohomological ((1 : ℤ), (-1 : ℤ)) 3 (by norm_num)
    ((-2 : ℤ) : EInt) ((-1 : ℤ) : EInt) ((0 : ℤ) : EInt) (by norm_num) rfl (by norm_num) 0
    (by norm_num)]
  have : Mono (spectralObject.δ (homOfLE (coe_le_coe_of_le (by norm_num : (-2 : ℤ) ≤ -1)))
      (homOfLE (coe_le_coe_of_le (by norm_num : (-1 : ℤ) ≤ 0))) 0 (0 + 1)) := mono_δ
  rw [kernelSubobject, Subobject.mk_eq_bot_iff_zero]
  exact (cancel_mono _).1 (by rw [kernel.condition, zero_comp])

end TauCeti.Examples.TimesTwo
