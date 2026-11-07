/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Pullback
public import Mathlib.RingTheory.Localization.Module
import TauCeti.RingTheory.FormalGlueing.Torsion
import TauCeti.Algebra.Module.Torsion.PrimaryComponent

/-!
# Injectivity for the compatible-pairs construction in formal gluing

Let `R → S` be flat and induce `R/I ≅ S/IS`, with `I` finitely generated. Suppose
`f : M → P` exhibits the `S`-module `P` as the scalar extension of `M`, and an `S`-linear
map `g : N → P` is injective off `V(IS)`. Then the comparison
`S ⊗[R] ker (f.coprod (-g)) → N` is injective.

This is the kernel-vanishing step for the actual compatible-pairs module in the proof
of formal gluing, Stacks, Proposition 15.91.16 (05ER). It does not assert surjectivity
of the comparison. The principal-open comparison and descent of extensions supply
separate steps in reconstruction.

The kernel of `g` is `IS`-power torsion, so its multiplication comparison is an
isomorphism by `TauCeti.isBaseChange_of_primaryComponent_eq_top` (Stacks 05EC).
The linear-algebra argument is `LinearMap.injective_liftBaseChange_snd_ker_coprod`.
-/

public section

open Function TensorProduct

namespace LinearMap

variable {R S M N P : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Module.Flat R S] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]

/-- For formal-gluing data, the scalar-extension comparison from the module of compatible
pairs to the prescribed `S`-module is injective. Only injectivity, rather than bijectivity,
of the map on the complementary principal opens is needed. -/
theorem injective_liftBaseChange_snd_ker_coprod_of_formalGlueing
    (f : M →ₗ[R] P) (g : N →ₗ[S] P) (hf : IsBaseChange S f) (G : Finset R)
    (hG : Bijective (Ideal.quotientMap ((Ideal.span (G : Set R)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map))
    (hloc : ∀ r ∈ G, Injective (LocalizedModule.map (.powers (algebraMap R S r)) g)) :
    Injective (((LinearMap.snd R M N).domRestrict
      (f.coprod (-g.restrictScalars R)).ker).liftBaseChange S) := by
  classical
  have ht : ((Ideal.span (G : Set R)).map (algebraMap R S)).primaryComponent g.ker = ⊤ := by
    rw [Ideal.map_span, ← Finset.coe_image]
    apply top_unique
    intro n _
    rw [Ideal.mem_primaryComponent_span_iff]
    intro s hs
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
    have hn : LocalizedModule.mkLinearMap (.powers (algebraMap R S r)) N n.val = 0 := by
      apply (injective_iff_map_eq_zero _).mp (hloc r hr)
      simp
    obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_zero_iff (.powers (algebraMap R S r))
      (LocalizedModule.mkLinearMap (.powers (algebraMap R S r)) N)).mp hn
    obtain ⟨k, hk⟩ := a.2
    refine ⟨k, Subtype.ext ?_⟩
    simpa only [Submodule.coe_smul, ZeroMemClass.coe_zero, Submonoid.smul_def, ← hk] using ha
  have hg := TauCeti.isBaseChange_of_primaryComponent_eq_top hG ht
  exact injective_liftBaseChange_snd_ker_coprod f g hf.1 hg.1

end LinearMap
