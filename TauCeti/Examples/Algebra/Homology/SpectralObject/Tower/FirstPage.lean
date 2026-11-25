/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Homology.SpectralObject.FirstPageFin
import TauCeti.Algebra.Homology.SpectralObject.SpectralSequenceMap
import TauCeti.Algebra.Homology.SpectralObject.Tower.FirstPage

/-!
# Checks for the towers of the spectral sequence of a spectral object through the first page

The general statements specialize, with their explicit indices, to the recipes
`coreE₂Cohomological` and `coreE₂CohomologicalFin l`.

* For `X` indexed by `EInt` at `(p, q)` with `n = p + q`: `Z_r` is the kernel of
  `δ : H^n(q ≤ q + 1) ⟶ H^{n+1}(q - r + 2 ≤ q)` and `B_r` the image of
  `δ : H^{n-1}(q + 1 ≤ q + r - 1) ⟶ H^n(q ≤ q + 1)`.
* For `X` indexed by `Fin (l + 1)` at `(p, q)`, with `l = 2`, `r = 3` and `q = 1`: the clamped
  indices are `(0, 1, 2, 2)`, so `Z_3` is the kernel of `δ : H^n(1 ≤ 2) ⟶ H^{n+1}(0 ≤ 1)` and
  `B_3` the image of `δ : H^{n-1}(2 ≤ 2) ⟶ H^n(1 ≤ 2)`; this source is `0`, so `B_3 = ⊥`.
* On the first page `r = 2` of the recipe `coreE₂Cohomological`, the formulas give `Z_2 = ⊤` and
  `B_2 = ⊥`: the target `H^{n+1}(q ≤ q)` of the first `δ` and the source `H^{n-1}(q + 1 ≤ q + 1)` of
  the second are `0`.
* Naturality of the towers in the spectral object is the naturality of the towers of any spectral
  sequence (`CategoryTheory.SpectralSequence.cyclesSubobject_le_pullback`), applied to the induced
  morphism `spectralSequenceMap data φ`.
-/

namespace TauCeti.Examples

open CategoryTheory Limits Abelian Abelian.SpectralObject ComposableArrows

variable {C : Type*} [Category* C] [Abelian C]

example (X : SpectralObject C EInt) [X.HasSpectralSequence coreE₂Cohomological] (p q r : ℤ)
    (hr : 2 ≤ r) :
    (X.spectralSequence coreE₂Cohomological).cyclesSubobject (p, q) r hr =
      kernelSubobject ((X.spectralSequenceFirstPageXIso coreE₂Cohomological (p, q) q
          ((q + 1 : ℤ) : EInt) rfl rfl (p + q) rfl).hom ≫
        X.δ (homOfLE (by simp; lia) : ((q - r + 2 : ℤ) : EInt) ⟶ (q : EInt))
          (homOfLE (by simp) : (q : EInt) ⟶ ((q + 1 : ℤ) : EInt)) (p + q) (p + q + 1)) :=
  X.cyclesSubobject_spectralSequence_eq_kernelSubobject_δ coreE₂Cohomological (p, q) r hr
    _ _ _ rfl rfl rfl _ rfl

example (X : SpectralObject C EInt) [X.HasSpectralSequence coreE₂Cohomological] (p q r : ℤ)
    (hr : 2 ≤ r) :
    (X.spectralSequence coreE₂Cohomological).boundariesSubobject (p, q) r hr =
      imageSubobject
        (X.δ (homOfLE (by simp) : (q : EInt) ⟶ ((q + 1 : ℤ) : EInt))
          (homOfLE (by simp; lia) : ((q + 1 : ℤ) : EInt) ⟶ ((q + r - 1 : ℤ) : EInt))
          (p + q - 1) (p + q) ≫
        (X.spectralSequenceFirstPageXIso coreE₂Cohomological (p, q) q ((q + 1 : ℤ) : EInt)
          rfl rfl (p + q) rfl).inv) :=
  X.boundariesSubobject_spectralSequence_eq_imageSubobject_δ coreE₂Cohomological (p, q) r hr
    _ _ _ rfl rfl rfl _ rfl

-- Clamped indices: for `l = 2`, `r = 3` and `q = 1`, the indices are `(0, 1, 2, 2)`.
example (X : SpectralObject C (Fin 3)) (p : ℤ) :
    (X.spectralSequence (coreE₂CohomologicalFin 2)).cyclesSubobject (p, 1) 3 (by lia) =
      kernelSubobject ((X.spectralSequenceFirstPageXIso (coreE₂CohomologicalFin 2) (p, 1) 1 2
          rfl rfl (p + 1) rfl).hom ≫
        X.δ (homOfLE (by decide) : (0 : Fin 3) ⟶ 1) (homOfLE (by decide) : (1 : Fin 3) ⟶ 2)
          (p + 1) (p + 1 + 1)) :=
  X.cyclesSubobject_spectralSequence_eq_kernelSubobject_δ (coreE₂CohomologicalFin 2) (p, 1) 3
    (by lia) _ _ _ (by ext; simp) rfl rfl _ rfl

-- At `q = 1` nothing enters the top row on the page `3`: the source `H^{n-1}(2 ≤ 2)` is `0`.
example (X : SpectralObject C (Fin 3)) (p : ℤ) :
    (X.spectralSequence (coreE₂CohomologicalFin 2)).boundariesSubobject (p, 1) 3 (by lia) = ⊥ := by
  rw [X.boundariesSubobject_spectralSequence_eq_imageSubobject_δ (coreE₂CohomologicalFin 2)
    (p, 1) 3 (by lia) 1 2 2 rfl rfl (by ext; simp [Fin.clamp]) (p + 1) rfl]
  convert (imageSubobject_zero : imageSubobject
    (0 : _ ⟶ ((X.spectralSequence (coreE₂CohomologicalFin 2)).page 2).X (p, 1)) = ⊥) using 2
  exact (X.isZero_H_obj_of_isIso _ ⟨⟨𝟙 _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
    _).eq_of_src _ _

-- On the first page nothing leaves `(p, q)`: the target `H^{n+1}(q ≤ q)` of `δ` is `0`.
example (X : SpectralObject C EInt) [X.HasSpectralSequence coreE₂Cohomological] (p q : ℤ) :
    (X.spectralSequence coreE₂Cohomological).cyclesSubobject (p, q) 2 le_rfl = ⊤ := by
  rw [X.cyclesSubobject_spectralSequence_eq_kernelSubobject_δ coreE₂Cohomological (p, q) 2 le_rfl
    q q ((q + 1 : ℤ) : EInt) (by simp) rfl rfl _ rfl]
  convert kernelSubobject_zero using 2
  exact (X.isZero_H_obj_of_isIso _ ⟨⟨𝟙 _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
    _).eq_of_tgt _ _

-- On the first page nothing enters `(p, q)`: the source `H^{n-1}(q + 1 ≤ q + 1)` of `δ` is `0`.
example (X : SpectralObject C EInt) [X.HasSpectralSequence coreE₂Cohomological] (p q : ℤ) :
    (X.spectralSequence coreE₂Cohomological).boundariesSubobject (p, q) 2 le_rfl = ⊥ := by
  rw [X.boundariesSubobject_spectralSequence_eq_imageSubobject_δ coreE₂Cohomological (p, q) 2
    le_rfl q ((q + 1 : ℤ) : EInt) ((q + 1 : ℤ) : EInt) rfl rfl (by simp; lia) _ rfl]
  convert (imageSubobject_zero : imageSubobject
    (0 : _ ⟶ ((X.spectralSequence coreE₂Cohomological).page 2).X (p, q)) = ⊥) using 2
  exact (X.isZero_H_obj_of_isIso _ ⟨⟨𝟙 _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
    _).eq_of_src _ _

-- Naturality in the spectral object, through the first-page component of `spectralSequenceMap`.
example {ι κ : Type*} [Preorder ι] {X Y : SpectralObject C ι} (φ : X ⟶ Y)
    {c : ℤ → ComplexShape κ} {r₀ : ℤ} (data : SpectralSequenceDataCore ι c r₀)
    [X.HasSpectralSequence data] [Y.HasSpectralSequence data] (pq : κ) (r : ℤ) (hr : r₀ ≤ r) :
    (X.spectralSequence data).cyclesSubobject pq r hr ≤
      (Subobject.pullback (spectralSequencePageXMap data φ r₀ le_rfl pq)).obj
        ((Y.spectralSequence data).cyclesSubobject pq r hr) := by
  simpa using (X.spectralSequence data).cyclesSubobject_le_pullback pq
    (spectralSequenceMap data φ) r hr

end TauCeti.Examples
