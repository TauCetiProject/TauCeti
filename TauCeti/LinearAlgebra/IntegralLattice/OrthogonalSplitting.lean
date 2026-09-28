/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Projection

/-!
# Orthogonal splitting over the integers

If the restricted pairing on a sublattice is perfect, the ambient lattice splits as that
submodule and its integral orthogonal complement. This is the integral analogue of orthogonal
splitting over a field; nondegeneracy alone does not give a splitting over `ℤ`.

The projection is obtained by representing the functional `y ↦ B(y,x)` on the submodule
through its perfect pairing. No nondegeneracy assumption on the ambient lattice is needed.
-/

public section

namespace TauCeti

universe u

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- Restrict pairing with a lattice vector to an integral submodule. -/
private noncomputable def pairingToDual (L : IntegralLattice V) (S : Submodule ℤ L) :
    L →ₗ[ℤ] Module.Dual ℤ S where
  toFun x :=
    { toFun := fun y ↦ L.integralForm y x
      map_add' := by
        intro y z
        exact congrArg (fun f : L →ₗ[ℤ] ℤ ↦ f x) (L.integralForm.map_add y z)
      map_smul' := by
        intro a y
        exact congrArg (fun f : L →ₗ[ℤ] ℤ ↦ f x) (L.integralForm.map_smul a y) }
  map_add' := by
    intro x y
    ext z
    exact (L.integralForm z).map_add x y
  map_smul' := by
    intro a x
    ext z
    exact (L.integralForm z).map_smul a x

/-- A submodule with perfect restricted pairing is complementary to its integral
orthogonal complement. -/
theorem isCompl_integralOrthogonal_of_bijective (L : IntegralLattice V)
    (S : Submodule ℤ L) (h : Function.Bijective (L.integralForm.restrict S)) :
    IsCompl S (L.integralForm.orthogonal S) := by
  let e : S ≃ₗ[ℤ] Module.Dual ℤ S :=
    LinearEquiv.ofBijective (L.integralForm.restrict S) h
  let p : L →ₗ[ℤ] S := e.symm.toLinearMap.comp (pairingToDual L S)
  have hp : ∀ y : S, p y = y := by
    intro y
    apply e.injective
    ext z
    simp [p, e, pairingToDual, LinearMap.BilinForm.restrict_apply, L.isSymm_integralForm.eq]
  have hker : LinearMap.ker p = L.integralForm.orthogonal S := by
    ext x
    rw [LinearMap.mem_ker, ← e.map_eq_zero_iff]
    have hpx : e (p x) = pairingToDual L S x := by simp [p]
    rw [hpx]
    constructor
    · intro hx
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro y hy
      have hy' := congrArg (fun f : Module.Dual ℤ S ↦ f ⟨y, hy⟩) hx
      simpa [pairingToDual] using hy'
    · intro hx
      ext y
      exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) y y.property
  rw [← hker]
  exact LinearMap.isCompl_of_proj hp

/-- A vector of unit norm spans an orthogonal direct summand of an integral lattice. -/
theorem isCompl_integralOrthogonal_span_of_isUnit (L : IntegralLattice V) (x : L)
    (hx : IsUnit (L.integralForm x x)) :
    IsCompl (ℤ ∙ x) (L.integralForm.orthogonal (ℤ ∙ x)) := by
  obtain ⟨a, ha⟩ := isUnit_iff_exists_inv.mp hx
  have ha' : a * L.integralForm x x = 1 := by simpa [mul_comm] using ha
  let S : Submodule ℤ L := ℤ ∙ x
  let p : L →ₗ[ℤ] S :=
    { toFun := fun y ↦ ⟨(a * L.integralForm x y) • x,
        Submodule.smul_mem S _ (Submodule.mem_span_singleton_self x)⟩
      map_add' := by
        intro y z
        apply Subtype.ext
        simp only [map_add, mul_add, add_smul, Submodule.coe_add]
      map_smul' := by
        intro b y
        apply Subtype.ext
        simp only [map_smul, zsmul_eq_mul, Submodule.coe_smul]
        rw [smul_smul]
        congr 1
        simp only [RingHom.id_apply, Int.cast_id]
        ring }
  have hp : ∀ y : S, p y = y := by
    intro y
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp y.property
    have hpx : p x = ⟨x, Submodule.mem_span_singleton_self x⟩ := by
      apply Subtype.ext
      simp [p, ha']
    calc
      p y = p (b • x) := congrArg p hb.symm
      _ = b • p x := map_smul p b x
      _ = y := by
        rw [hpx]
        exact Subtype.ext hb
  have hker : LinearMap.ker p = L.integralForm.orthogonal S := by
    ext y
    rw [LinearMap.mem_ker]
    have horth : y ∈ L.integralForm.orthogonal S ↔ L.integralForm x y = 0 := by
      constructor
      · intro hy
        exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hy) x
          (Submodule.mem_span_singleton_self x)
      · intro hy
        apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
        intro z hz
        obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hz
        rw [← hb, map_smul]
        simp [hy]
    rw [horth]
    constructor
    · intro hy
      have h := congrArg (fun z : S ↦ L.integralForm x (z : L)) hy
      have h' : (a * L.integralForm x y) * L.integralForm x x = 0 := by
        simpa [p, map_smul] using h
      calc
        L.integralForm x y = (a * L.integralForm x x) * L.integralForm x y := by
          rw [ha']; ring
        _ = (a * L.integralForm x y) * L.integralForm x x := by ring
        _ = 0 := h'
    · intro hy
      apply Subtype.ext
      simp [p, hy]
  rw [← hker]
  exact LinearMap.isCompl_of_proj hp

end IntegralLattice

end TauCeti
