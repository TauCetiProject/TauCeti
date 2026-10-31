/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Basic
public import TauCeti.Analysis.Complex.Germ.Algebra

/-!
# From holomorphic functions to germs

A holomorphic function on an open neighbourhood of a set defines a germ near that set.
The maps `HolomorphicFunctions.toGerm` commute with restriction, and every holomorphic
germ arises this way. Two functions define the same germ precisely when their restrictions
agree on some common open neighbourhood.

Compatible algebra homomorphisms on these neighbourhoods therefore descend uniquely to
`holomorphicGerms s`. This allows constructions on open domains, such as contour functional
calculi, to be assembled without choosing representatives of germs in their public interface.
No compactness assumption on the base set is needed.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
-/

public noncomputable section

open Filter Set Topology TopologicalSpace

namespace TauCeti.HolomorphicFunctions

variable {s : Set ℂ} {U V : Opens ℂ}

/-- Send a holomorphic function on an open neighbourhood of `s` to its germ near `s`. -/
def toGerm (hs : s ⊆ U) : holomorphicFunctions U →ₐ[ℂ] holomorphicGerms s where
  toFun f := holomorphicGerms.ofFun (extend f)
    (((differentiableOn_extend f).analyticOnNhd U.isOpen).mono hs)
  map_zero' := by
    apply Subtype.ext
    rw [holomorphicGerms.coe_ofFun, Subalgebra.coe_zero, ← Germ.coe_zero]
    apply Germ.coe_eq.mpr
    filter_upwards [U.isOpen.mem_nhdsSet.mpr hs] with z hz
    simpa using extend_apply (0 : holomorphicFunctions U) ⟨z, hz⟩
  map_one' := by
    apply Subtype.ext
    rw [holomorphicGerms.coe_ofFun, Subalgebra.coe_one, ← Germ.coe_one]
    apply Germ.coe_eq.mpr
    filter_upwards [U.isOpen.mem_nhdsSet.mpr hs] with z hz
    simpa using extend_apply (1 : holomorphicFunctions U) ⟨z, hz⟩
  map_add' f g := by
    apply Subtype.ext
    simp only [Subalgebra.coe_add, holomorphicGerms.coe_ofFun, ← Germ.coe_add]
    apply Germ.coe_eq.mpr
    filter_upwards [U.isOpen.mem_nhdsSet.mpr hs] with z hz
    simpa only [Pi.add_apply, extend_apply _ ⟨z, hz⟩, ContinuousMap.add_apply] using
      congrArg (fun h : C(U, ℂ) => h ⟨z, hz⟩) ((holomorphicFunctions U).coe_add f g)
  map_mul' f g := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, holomorphicGerms.coe_ofFun, ← Germ.coe_mul]
    apply Germ.coe_eq.mpr
    filter_upwards [U.isOpen.mem_nhdsSet.mpr hs] with z hz
    simpa only [Pi.mul_apply, extend_apply _ ⟨z, hz⟩, ContinuousMap.mul_apply] using
      congrArg (fun h : C(U, ℂ) => h ⟨z, hz⟩) ((holomorphicFunctions U).coe_mul f g)
  commutes' c := by
    apply Subtype.ext
    rw [holomorphicGerms.coe_ofFun, Subalgebra.coe_algebraMap, Germ.algebraMap_eq]
    apply Germ.coe_eq.mpr
    filter_upwards [U.isOpen.mem_nhdsSet.mpr hs] with z hz
    simpa using extend_apply (algebraMap ℂ (holomorphicFunctions U) c) ⟨z, hz⟩

/-- An ambient holomorphic representative gives its original function germ. -/
@[simp]
theorem toGerm_of (hs : s ⊆ U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) :
    toGerm hs (of U f hf) = holomorphicGerms.ofFun f ((hf.analyticOnNhd U.isOpen).mono hs) := by
  refine (holomorphicGerms.ofFun_eq_iff
    (((differentiableOn_extend _).analyticOnNhd U.isOpen).mono hs)
    ((hf.analyticOnNhd U.isOpen).mono hs)).mpr ?_
  filter_upwards [U.isOpen.mem_nhdsSet.mpr hs] with z hz
  simpa only [of_apply] using extend_apply (of U f hf) ⟨z, hz⟩

/-- Evaluating a function germ at a point of the base set recovers the function value. -/
@[simp]
theorem eval_toGerm (hs : s ⊆ U) (x : ℂ) (hx : x ∈ s) (f : holomorphicFunctions U) :
    holomorphicGerms.eval x hx (toGerm hs f) = f.val ⟨x, hs hx⟩ := by
  exact (holomorphicGerms.eval_ofFun x hx (extend f)
    (((differentiableOn_extend f).analyticOnNhd U.isOpen).mono hs)).trans
      (extend_apply f ⟨x, hs hx⟩)

/-- Shrinking the open domain does not change the germ. -/
@[simp]
theorem toGerm_restrict (hs : s ⊆ V) (hVU : V ≤ U) (f : holomorphicFunctions U) :
    toGerm hs (restrict hVU f) = toGerm (hs.trans hVU) f := by
  refine (holomorphicGerms.ofFun_eq_iff
    (((differentiableOn_extend _).analyticOnNhd V.isOpen).mono hs)
    (((differentiableOn_extend _).analyticOnNhd U.isOpen).mono (hs.trans hVU))).mpr ?_
  filter_upwards [V.isOpen.mem_nhdsSet.mpr hs] with z hz
  rw [extend_apply _ ⟨z, hz⟩, restrict_apply, extend_apply _ ⟨z, hVU hz⟩]

/-- Restricting the base set commutes with taking a function germ. -/
@[simp]
theorem restrict_toGerm {t : Set ℂ} (ht : t ⊆ s) (hs : s ⊆ U)
    (f : holomorphicFunctions U) :
    holomorphicGerms.restrict ht (toGerm hs f) = toGerm (ht.trans hs) f := by
  exact holomorphicGerms.restrict_ofFun ht (extend f)
    (((differentiableOn_extend f).analyticOnNhd U.isOpen).mono hs)

/-- Equality of function germs means equality on some smaller common open neighbourhood. -/
theorem toGerm_eq_iff (hsU : s ⊆ U) (hsV : s ⊆ V)
    (f : holomorphicFunctions U) (g : holomorphicFunctions V) :
    toGerm hsU f = toGerm hsV g ↔
      ∃ (W : Opens ℂ) (_ : s ⊆ W) (hWU : W ≤ U) (hWV : W ≤ V),
        restrict hWU f = restrict hWV g := by
  constructor
  · intro h
    obtain ⟨N, hN, hsN, heq⟩ := eventually_nhdsSet_iff_exists.mp
      ((holomorphicGerms.ofFun_eq_iff
        (((differentiableOn_extend f).analyticOnNhd U.isOpen).mono hsU)
        (((differentiableOn_extend g).analyticOnNhd V.isOpen).mono hsV)).mp h)
    refine ⟨⟨N, hN⟩ ⊓ U ⊓ V, fun z hz => ⟨⟨hsN hz, hsU hz⟩, hsV hz⟩,
      fun z hz => hz.1.2, fun z hz => hz.2, ?_⟩
    apply Subtype.ext
    ext z
    simp only [restrict_apply]
    exact (extend_apply f ⟨z, z.property.1.2⟩).symm.trans
      ((heq z z.property.1.1).trans (extend_apply g ⟨z, z.property.2⟩))
  · rintro ⟨W, hsW, hWU, hWV, hfg⟩
    rw [← toGerm_restrict hsW hWU, ← toGerm_restrict hsW hWV, hfg]

end TauCeti.HolomorphicFunctions

namespace TauCeti.holomorphicGerms

/-- Every holomorphic germ is represented by a holomorphic function on an open neighbourhood. -/
theorem exists_toGerm_eq {s : Set ℂ} (g : holomorphicGerms s) :
    ∃ (U : Opens ℂ) (hs : s ⊆ U) (f : holomorphicFunctions U),
      HolomorphicFunctions.toGerm hs f = g := by
  obtain ⟨U, f, hU, hs, hf, hfg⟩ := mem_holomorphicGerms_iff_exists_open.mp g.property
  refine ⟨⟨U, hU⟩, hs, HolomorphicFunctions.of ⟨U, hU⟩ f hf, ?_⟩
  rw [HolomorphicFunctions.toGerm_of]
  apply Subtype.ext
  simpa only [coe_ofFun] using hfg

section Lift

variable {s : Set ℂ} {B : Type*} [Semiring B] [Algebra ℂ B]
  (Φ : ∀ (U : Opens ℂ), s ⊆ U → holomorphicFunctions U →ₐ[ℂ] B)
  (hΦ : ∀ (U V : Opens ℂ) (hs : s ⊆ V) (hVU : V ≤ U) (f : holomorphicFunctions U),
    Φ V hs (HolomorphicFunctions.restrict hVU f) = Φ U (hs.trans hVU) f)

include hΦ in
private theorem exists_lift_value (g : holomorphicGerms s) :
    ∃ b : B, ∀ (U : Opens ℂ) (hs : s ⊆ U) (f : holomorphicFunctions U),
      HolomorphicFunctions.toGerm hs f = g → Φ U hs f = b := by
  obtain ⟨U, hsU, f, rfl⟩ := exists_toGerm_eq g
  refine ⟨Φ U hsU f, ?_⟩
  intro V hsV k hk
  obtain ⟨W, hsW, hWV, hWU, heq⟩ :=
    (HolomorphicFunctions.toGerm_eq_iff hsV hsU k f).mp hk
  rw [← hΦ V W hsW hWV k, heq, hΦ U W hsW hWU f]

private def liftFun (g : holomorphicGerms s) : B :=
  Classical.choose (exists_lift_value Φ hΦ g)

private theorem liftFun_toGerm (U : Opens ℂ) (hs : s ⊆ U) (f : holomorphicFunctions U) :
    liftFun Φ hΦ (HolomorphicFunctions.toGerm hs f) = Φ U hs f :=
  (Classical.choose_spec (exists_lift_value Φ hΦ (HolomorphicFunctions.toGerm hs f))
    U hs f rfl).symm

/-- Compatible algebra homomorphisms on open neighbourhoods descend to holomorphic germs.
Compatibility means that shrinking a neighbourhood does not change the image of a function. -/
def lift : holomorphicGerms s →ₐ[ℂ] B where
  toFun := liftFun Φ hΦ
  map_zero' := by
    rw [← map_zero (HolomorphicFunctions.toGerm (U := ⊤) (subset_univ s)), liftFun_toGerm, map_zero]
  map_one' := by
    rw [← map_one (HolomorphicFunctions.toGerm (U := ⊤) (subset_univ s)), liftFun_toGerm, map_one]
  map_add' a b := by
    obtain ⟨U, hsU, f, rfl⟩ := exists_toGerm_eq a
    obtain ⟨V, hsV, g, rfl⟩ := exists_toGerm_eq b
    let hs : s ⊆ (U ⊓ V : Opens ℂ) := fun z hz => ⟨hsU hz, hsV hz⟩
    rw [← HolomorphicFunctions.toGerm_restrict hs inf_le_left f,
      ← HolomorphicFunctions.toGerm_restrict hs inf_le_right g, ← map_add, liftFun_toGerm]
    simp only [liftFun_toGerm, map_add]
  map_mul' a b := by
    obtain ⟨U, hsU, f, rfl⟩ := exists_toGerm_eq a
    obtain ⟨V, hsV, g, rfl⟩ := exists_toGerm_eq b
    let hs : s ⊆ (U ⊓ V : Opens ℂ) := fun z hz => ⟨hsU hz, hsV hz⟩
    rw [← HolomorphicFunctions.toGerm_restrict hs inf_le_left f,
      ← HolomorphicFunctions.toGerm_restrict hs inf_le_right g, ← map_mul, liftFun_toGerm]
    simp only [liftFun_toGerm, map_mul]
  commutes' c := by
    rw [← AlgHom.commutes (HolomorphicFunctions.toGerm (U := ⊤) (subset_univ s)) c,
      liftFun_toGerm, AlgHom.commutes]

/-- The descended homomorphism agrees with the given one on each open neighbourhood. -/
@[simp]
theorem lift_toGerm (U : Opens ℂ) (hs : s ⊆ U) (f : holomorphicFunctions U) :
    lift Φ hΦ (HolomorphicFunctions.toGerm hs f) = Φ U hs f :=
  liftFun_toGerm Φ hΦ U hs f

/-- Homomorphisms on holomorphic germs are determined by their values on open domains. -/
@[ext]
theorem algHom_ext {φ ψ : holomorphicGerms s →ₐ[ℂ] B}
    (h : ∀ (U : Opens ℂ) (hs : s ⊆ U) (f : holomorphicFunctions U),
      φ (HolomorphicFunctions.toGerm hs f) = ψ (HolomorphicFunctions.toGerm hs f)) : φ = ψ := by
  ext g
  obtain ⟨U, hs, f, rfl⟩ := exists_toGerm_eq g
  exact h U hs f

/-- The descended homomorphism is the unique homomorphism with the prescribed restrictions. -/
theorem lift_unique (φ : holomorphicGerms s →ₐ[ℂ] B)
    (hφ : ∀ (U : Opens ℂ) (hs : s ⊆ U) (f : holomorphicFunctions U),
      φ (HolomorphicFunctions.toGerm hs f) = Φ U hs f) : φ = lift Φ hΦ := by
  apply algHom_ext
  intro U hs f
  rw [hφ, lift_toGerm]

end Lift

end TauCeti.holomorphicGerms
