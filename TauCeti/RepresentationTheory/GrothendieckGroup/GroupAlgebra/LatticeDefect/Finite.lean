/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.Basic

/-!
# Vanishing of the lattice defect for finite modules

The difference between the reduction and torsion classes of a finite module is zero in the
exact Grothendieck group, even though the two representations need not be isomorphic.
Together with additivity, this is the finite-module input to invariance of lattice defects
under inclusions with finite cokernel.

The coefficient ring and the acting monoid are arbitrary.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Section VII.3, (7.3.3).
-/

public section

namespace TauCeti

open Function
open scoped MonoidAlgebra Pointwise

attribute [local instance high] Submodule.module Submodule.Quotient.module TensorProduct.instModule

universe u

variable (k G : Type u) [CommRing k] [Monoid G] (ℓ : ℕ)

/-- A module killed by `ℓ` has zero lattice defect: both its `ℓ`-torsion and its reduction
modulo `ℓ` are equivariantly isomorphic to the original module. -/
theorem latticeDefect_eq_zero_of_isTorsionBy (V : Type u) [AddCommGroup V]
    [DistribMulAction G V] [Finite V] (hV : Module.IsTorsionBy ℤ V (ℓ : ℤ)) :
    letI := Fintype.ofFinite V
    latticeDefect k G ℓ V = 0 := by
  let := Fintype.ofFinite V
  have := AddMonoid.FG.to_moduleFinite_int (G := V)
  let ρ := Representation.ofDistribMulAction ℤ G V
  have hbot : (ℓ : ℤ) • (⊤ : Submodule ℤ V) = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨y, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x (ℓ : ℤ) ⊤).mp hx
    simpa using hV (x := y)
  let eQ : (ρ.quotSMulTop (ℓ : ℤ)).Equiv ρ :=
    { toLinearEquiv := ((ℓ : ℤ) • (⊤ : Submodule ℤ V)).quotEquivOfEqBot hbot
      isIntertwining' g := by
        ext x
        simp }
  let eT : (ρ.torsionBy (ℓ : ℤ)).Equiv ρ :=
    { toLinearEquiv := LinearEquiv.ofBijective (Submodule.torsionBy ℤ V (ℓ : ℤ)).subtype
        ⟨Subtype.coe_injective, fun x => ⟨⟨x, (Submodule.mem_torsionBy_iff _ _).mpr
          (hV (x := x))⟩, rfl⟩⟩
      isIntertwining' g := by
        ext x
        exact Representation.coe_torsionBy_apply ρ (ℓ : ℤ) g x }
  rw [latticeDefect_def, reductionK0_congr k eQ, reductionK0_congr k eT, sub_self]

private theorem latticeDefect_eq_zero_of_injective_zsmul (W : Type u) [AddCommGroup W]
    [DistribMulAction G W] [Finite W] (hf : Injective (fun x : W => (ℓ : ℤ) • x)) :
    letI := Fintype.ofFinite W
    latticeDefect k G ℓ W = 0 := by
  let := Fintype.ofFinite W
  have hsurj : Surjective (fun x : W => (ℓ : ℤ) • x) :=
    Finite.injective_iff_surjective.mp hf
  have htop : (ℓ : ℤ) • (⊤ : Submodule ℤ W) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y, hy⟩ := hsurj x
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨y, trivial, hy⟩
  have : Subsingleton (QuotSMulTop (ℓ : ℤ) W) :=
    Submodule.Quotient.subsingleton_iff.mpr htop
  have : Subsingleton (Submodule.torsionBy ℤ W (ℓ : ℤ)) :=
    ⟨fun x y => Subtype.ext <| hf <| by
      exact ((Submodule.mem_torsionBy_iff _ _).mp x.property).trans
        ((Submodule.mem_torsionBy_iff _ _).mp y.property).symm⟩
  rw [latticeDefect_def]
  simp

/- The argument uses multiplication by a prime `ℓ`. Its kernel is killed by `ℓ` and therefore has
zero defect. If multiplication is injective, finiteness makes it bijective, so both reduction
and torsion vanish. Otherwise its image has smaller cardinality, and additivity reduces the
claim to that image. -/

/-- A finite module has zero lattice defect in the exact Grothendieck group. The torsion and
reduction representations have the same class; no equivariant isomorphism is asserted. -/
@[simp]
theorem latticeDefect_eq_zero_of_finite [Fact ℓ.Prime] (V : Type u) [AddCommGroup V]
    [DistribMulAction G V] [Finite V] :
    letI := Fintype.ofFinite V
    latticeDefect k G ℓ V = 0 := by
  classical
  let := Fintype.ofFinite V
  suffices H : ∀ n (W : Type u) [AddCommGroup W] [DistribMulAction G W] [Fintype W],
      Nat.card W = n → latticeDefect k G ℓ W = 0 from H _ V rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ _ _ hn
    let f : W →+[G] W := SMulCommClass.toDistribMulActionHom G W (ℓ : ℤ)
    by_cases hf : Injective f
    · exact latticeDefect_eq_zero_of_injective_zsmul k G ℓ W hf
    · -- Reduce by the exact sequence from the torsion kernel to the multiplication image.
      -- The canonical integer-linear map has the same underlying function as `f`.
      let m := f.toAddMonoidHom.toIntLinearMap
      have hm (x : W) : m x = f x := rfl
      let T := Submodule.torsionBy ℤ W (ℓ : ℤ)
      let I := m.range
      let := Fintype.ofFinite T
      let := Fintype.ofFinite I
      -- Restrict the action to the kernel and image; Mathlib pulls back the action laws.
      let : SMul G T := ⟨fun g x => ⟨g • x, by
        rw [Submodule.mem_torsionBy_iff] at *
        rw [smul_comm, (Submodule.mem_torsionBy_iff _ _).mp x.property, smul_zero]⟩⟩
      let : DistribMulAction G T := Subtype.coe_injective.distribMulAction
        T.subtype.toAddMonoidHom (fun _ _ => rfl)
      let : SMul G I := ⟨fun g x => ⟨g • x, by
        obtain ⟨y, hy⟩ := x.property
        exact ⟨g • y, by simpa only [hm, map_smul f] using congrArg (g • ·) hy⟩⟩⟩
      let : DistribMulAction G I := Subtype.coe_injective.distribMulAction
        I.subtype.toAddMonoidHom (fun _ _ => rfl)
      let i : T →+[G] W :=
        { T.subtype.toAddMonoidHom with map_smul' := fun _ _ => rfl }
      let q : W →+[G] I :=
        { m.rangeRestrict.toAddMonoidHom with
          map_smul' := fun g x => Subtype.ext (map_smul f g x) }
      have hi : Injective i := Subtype.coe_injective
      have hq : Surjective q := m.surjective_rangeRestrict
      have hmker : m.ker = T := by
        ext x
        simp only [LinearMap.mem_ker, hm]
        rfl
      have hiq : Exact i q := LinearMap.exact_iff.mpr <| by
        rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype, hmker]
      -- Noninjectivity forces a strict decrease, so the image satisfies the induction hypothesis.
      have hlt : Nat.card I < n := by
        rw [← hn]
        refine lt_of_le_of_ne (Nat.card_le_card_of_surjective q hq) ?_
        intro hcard
        apply hf
        intro x y hxy
        exact (hq.bijective_of_nat_card_le hcard.ge).1 (Subtype.ext hxy)
      have hT : latticeDefect k G ℓ T = 0 :=
        latticeDefect_eq_zero_of_isTorsionBy k G ℓ T
          (Submodule.torsionBy_isTorsionBy _)
      rw [latticeDefect_add_of_exact k G ℓ i q hi hiq hq, hT,
        ih (Nat.card I) hlt I rfl, zero_add]

/-- An inclusion with finite cokernel preserves the lattice defect. The short exact sequence is
given by equivariant maps, so neither its source nor its middle term needs to be finite. -/
theorem latticeDefect_eq_of_exact_of_finite [Fact ℓ.Prime] {A B C : Type u}
    [AddCommGroup A] [DistribMulAction G A] [AddCommGroup B] [DistribMulAction G B]
    [AddCommGroup C] [DistribMulAction G C] [Finite C]
    (f : A →+[G] B) (g : B →+[G] C) (hf : Injective f) (hfg : Exact f g) (hg : Surjective g)
    [Finite (QuotSMulTop (ℓ : ℤ) A)] [Finite (Submodule.torsionBy ℤ A ℓ)]
    [Finite (QuotSMulTop (ℓ : ℤ) B)] [Finite (Submodule.torsionBy ℤ B ℓ)] :
    latticeDefect k G ℓ A = latticeDefect k G ℓ B := by
  let := Fintype.ofFinite C
  rw [latticeDefect_add_of_exact k G ℓ f g hf hfg hg,
    latticeDefect_eq_zero_of_finite k G ℓ C, add_zero]

end TauCeti
