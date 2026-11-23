/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Sewing

/-!
# Cylinder classes and Floer breaking

Fix a homotopy class `u` of cylinders from an input orbit `x₁` to an output orbit `x₀`: a Floer
cylinder, a continuation cylinder, or a PSS half-cylinder. Gluing a cap `D₁` of the input to `u`
gives a cap `glue D₁` of the output, and recapping the input by `B` recaps the glued cap by `B`.
The class `A = D₀ + u − D₁` of the cylinder relative to an output cap `D₀` is
`cylinderClass glue D₁ D₀ = D₀ -ᵥ glue D₁` in the period group `Γ`. This is the class in which the
counts of maps between capped generators are indexed: by the change of caps
(`TauCeti.Floer.cylinderClass_eq_add_sub`), a cylinder of class `A` relative to reference caps
`r₁`, `r₀` glues `D₁` to `D₀`, that is has class zero relative to `D₁` and `D₀`, exactly when
`A = (D₁ -ᵥ r₁) - (D₀ -ᵥ r₀)` (`TauCeti.Floer.cylinderClass_eq_zero_iff_eq_sub`). This is the class
over which the coefficient at `(D₁, D₀)` of a map of class-indexed counts sums
(`TauCeti.Floer.mapKernelOfMatrix_coefficientComparison_apply`). As for the
product class `TauCeti.Floer.productClass`, the topological energy `A₁(D₁) − A₀(D₀) + ω(A)` and the
index `μ₁(D₁) − μ₀(D₀) + 2 c₁(A)` do not depend on the choice of caps
(`TauCeti.Floer.sub_add_map_cylinderClass_eq`,
`TauCeti.Floer.sub_add_two_mul_chern_cylinderClass_eq`).

A pair of pants with one input fixed is a cylinder from the other input to the output, and its
product class is the cylinder class (`TauCeti.Floer.productClass_eq_cylinderClass_fst`,
`TauCeti.Floer.productClass_eq_cylinderClass_snd`). For a PSS plane `u`, itself a cap of its
orbit and counted in the class `r -ᵥ u` relative to a reference cap `r`, gluing it to a cylinder
gives the cap `glue u`, and `cylinderClass_eq_add_sub` says that the class of the glued plane is
the class of the cylinder plus the class of the plane.

When a sequence of Floer solutions breaks at an end, a cylinder splits off, and the classes of
the pieces add up to the class of the unbroken configuration whatever cap is chosen at the
intermediate orbit:

* a cylinder breaks into two cylinders (`TauCeti.Floer.cylinderClass_comp`);
* a pair of pants breaks off a cylinder at its output (`TauCeti.Floer.productClass_comp_out`);
* a pair of pants breaks off cylinders at its inputs (`TauCeti.Floer.productClass_comp_in`).

Together with the sewing of two pairs of pants
(`TauCeti.Floer.productClass_comp_fst`, `TauCeti.Floer.productClass_comp_snd`) these are the
class-addition laws behind the identities between counts given by the boundaries of
one-dimensional moduli spaces. They are torsor statements conditional on the equivariance of the
given gluing maps; the instances for caps of actual loops are in
`TauCeti.Geometry.Symplectic.Floer.Cap.Breaking`. No moduli space or count is constructed.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
-/

public section

namespace TauCeti.Floer

variable {S : Type*} [AddGroup S] {ω : S →+ ℝ} {c : S →+ ℤ}

section Cylinder

variable {C₁ C₀ : Type*} [AddTorsor (PeriodGroup ω c) C₀]

/-- The class `A = D₀ + u − D₁` of a cylinder `u` from an input orbit to an output orbit. Here
`glue D₁` is the cap of the output obtained by gluing the input cap `D₁` to `u`, and `D₀` is the
chosen output cap. In a reference basis the coefficient of the cylinder is weighted by the
Novikov monomial of `-A`. -/
def cylinderClass (glue : C₁ → C₀) (D₁ : C₁) (D₀ : C₀) : PeriodGroup ω c :=
  D₀ -ᵥ glue D₁

variable {glue : C₁ → C₀}

/-- The cylinder class is the difference of the output cap and the glued cap. -/
theorem cylinderClass_def (D₁ : C₁) (D₀ : C₀) : cylinderClass glue D₁ D₀ = D₀ -ᵥ glue D₁ :=
  (rfl)

/-- The cylinder class vanishes exactly when the output cap is the glued cap. -/
@[simp]
theorem cylinderClass_eq_zero_iff {D₁ : C₁} {D₀ : C₀} :
    cylinderClass glue D₁ D₀ = 0 ↔ D₀ = glue D₁ :=
  vsub_eq_zero_iff_eq

/-- A pair of pants with its second input cap fixed is a cylinder from its first input, and its
product class is the class of that cylinder. -/
theorem productClass_eq_cylinderClass_fst {C₂ : Type*} (glue : C₁ → C₂ → C₀) (D₁ : C₁) (D₂ : C₂)
    (D₀ : C₀) : productClass glue D₁ D₂ D₀ = cylinderClass (glue · D₂) D₁ D₀ := by
  rw [productClass_def, cylinderClass_def]

/-- A pair of pants with its first input cap fixed is a cylinder from its second input, and its
product class is the class of that cylinder. -/
theorem productClass_eq_cylinderClass_snd {C₂ : Type*} (glue : C₁ → C₂ → C₀) (D₁ : C₁) (D₂ : C₂)
    (D₀ : C₀) : productClass glue D₁ D₂ D₀ = cylinderClass (glue D₁) D₂ D₀ := by
  rw [productClass_def, cylinderClass_def]

/-- Recapping the output by `γ` adds `γ` to the cylinder class. -/
@[simp]
theorem cylinderClass_vadd_out (γ : PeriodGroup ω c) (D₁ : C₁) (D₀ : C₀) :
    cylinderClass glue D₁ (γ +ᵥ D₀) = γ + cylinderClass glue D₁ D₀ := by
  rw [cylinderClass_def, cylinderClass_def, vadd_vsub_assoc]

/-- If gluing is equivariant, recapping the input by `γ` subtracts `γ` from the cylinder
class. -/
theorem cylinderClass_vadd_in [VAdd (PeriodGroup ω c) C₁]
    (hglue : ∀ (γ : PeriodGroup ω c) D₁, glue (γ +ᵥ D₁) = γ +ᵥ glue D₁)
    (γ : PeriodGroup ω c) (D₁ : C₁) (D₀ : C₀) :
    cylinderClass glue (γ +ᵥ D₁) D₀ = cylinderClass glue D₁ D₀ - γ := by
  rw [cylinderClass_def, hglue, vsub_vadd_eq_vsub_sub, cylinderClass_def]

/-- If another gluing map `glue'` glues `D₁` to the cap glued by `glue`, recapped by `γ`, then
the cylinder class for `glue'` is the cylinder class for `glue` minus `γ`. -/
theorem cylinderClass_eq_sub_of_eq_vadd {glue' : C₁ → C₀} {γ : PeriodGroup ω c} {D₁ : C₁}
    (h : glue' D₁ = γ +ᵥ glue D₁) (D₀ : C₀) :
    cylinderClass glue' D₁ D₀ = cylinderClass glue D₁ D₀ - γ := by
  rw [cylinderClass_def, h, vsub_vadd_eq_vsub_sub, cylinderClass_def]

variable [AddTorsor (PeriodGroup ω c) C₁]

/-- Change of caps: if gluing is equivariant, the cylinder class for caps `D₁`, `D₀` is the
cylinder class for reference caps `r₁`, `r₀`, plus the recapping class of the output, minus the
recapping class of the input. -/
theorem cylinderClass_eq_add_sub
    (hglue : ∀ (γ : PeriodGroup ω c) D₁, glue (γ +ᵥ D₁) = γ +ᵥ glue D₁)
    (D₁ r₁ : C₁) (D₀ r₀ : C₀) :
    cylinderClass glue D₁ D₀ = cylinderClass glue r₁ r₀ + (D₀ -ᵥ r₀) - (D₁ -ᵥ r₁) := by
  conv_lhs => rw [← vsub_vadd D₁ r₁, ← vsub_vadd D₀ r₀]
  rw [cylinderClass_vadd_in hglue, cylinderClass_vadd_out]
  -- `PeriodGroup ω c` has no commutative instance for a general `S`, so compare areas and
  -- Chern numbers.
  refine PeriodGroup.ext ?_ ?_ <;> simp only [map_add, map_sub] <;> abel

/-- A cylinder of class `A` relative to reference caps `r₁`, `r₀` glues the cap `D₁` to the cap
`D₀` exactly when `A = (D₁ -ᵥ r₁) - (D₀ -ᵥ r₀)`: this is the class over which the coefficient at
`(D₁, D₀)` of a map of class-indexed counts sums
(`TauCeti.Floer.mapKernelOfMatrix_coefficientComparison_apply`). -/
theorem cylinderClass_eq_zero_iff_eq_sub
    (hglue : ∀ (γ : PeriodGroup ω c) D₁, glue (γ +ᵥ D₁) = γ +ᵥ glue D₁)
    (D₁ r₁ : C₁) (D₀ r₀ : C₀) :
    cylinderClass glue D₁ D₀ = 0 ↔ cylinderClass glue r₁ r₀ = (D₁ -ᵥ r₁) - (D₀ -ᵥ r₀) := by
  rw [cylinderClass_eq_add_sub hglue D₁ r₁ D₀ r₀, sub_eq_zero, eq_sub_iff_add_eq]

/-- Cap independence of `f₁ D₁ − f₀ D₀ + φ(A)` for a cylinder: if gluing is equivariant and the
functions `fᵢ` change by `φ γ` under recapping by `γ`, then this quantity takes the same value
for all choices of caps. With `φ = PeriodGroup.area ω c` and the action functionals as `fᵢ`, this
is the cap independence of the topological energy `A₁(D₁) − A₀(D₀) + ω(A)` of a cylinder. -/
theorem sub_add_map_cylinderClass_eq {A : Type*} [AddCommGroup A]
    (φ : PeriodGroup ω c →+ A) {f₁ : C₁ → A} {f₀ : C₀ → A}
    (hglue : ∀ (γ : PeriodGroup ω c) D₁, glue (γ +ᵥ D₁) = γ +ᵥ glue D₁)
    (hf₁ : ∀ (γ : PeriodGroup ω c) D, f₁ (γ +ᵥ D) = φ γ + f₁ D)
    (hf₀ : ∀ (γ : PeriodGroup ω c) D, f₀ (γ +ᵥ D) = φ γ + f₀ D)
    (D₁ D₁' : C₁) (D₀ D₀' : C₀) :
    f₁ D₁ - f₀ D₀ + φ (cylinderClass glue D₁ D₀) =
      f₁ D₁' - f₀ D₀' + φ (cylinderClass glue D₁' D₀') := by
  rw [← vsub_vadd D₁ D₁', ← vsub_vadd D₀ D₀', cylinderClass_vadd_out,
    cylinderClass_vadd_in hglue, hf₁, hf₀]
  simp only [map_add, map_sub]
  abel

/-- Cap independence of the index `μ₁(D₁) − μ₀(D₀) + 2 c₁(A)` of a cylinder, for gradings `mᵢ`
obeying the recapping law for twice the first Chern number. The Fredholm index of a Floer
cylinder in class `A` is this quantity. -/
theorem sub_add_two_mul_chern_cylinderClass_eq {m₁ : C₁ → ℤ} {m₀ : C₀ → ℤ}
    (hglue : ∀ (γ : PeriodGroup ω c) D₁, glue (γ +ᵥ D₁) = γ +ᵥ glue D₁)
    (hm₁ : ∀ (γ : PeriodGroup ω c) D, m₁ (γ +ᵥ D) = 2 * PeriodGroup.chern ω c γ + m₁ D)
    (hm₀ : ∀ (γ : PeriodGroup ω c) D, m₀ (γ +ᵥ D) = 2 * PeriodGroup.chern ω c γ + m₀ D)
    (D₁ D₁' : C₁) (D₀ D₀' : C₀) :
    m₁ D₁ - m₀ D₀ + 2 * PeriodGroup.chern ω c (cylinderClass glue D₁ D₀) =
      m₁ D₁' - m₀ D₀' + 2 * PeriodGroup.chern ω c (cylinderClass glue D₁' D₀') := by
  have key := sub_add_map_cylinderClass_eq ((2 : ℤ) • PeriodGroup.chern ω c) hglue
    (by simpa using hm₁) (by simpa using hm₀) D₁ D₁' D₀ D₀'
  simpa only [AddMonoidHom.zsmul_apply, Int.zsmul_eq_mul] using key

end Cylinder

section Breaking

variable {C₁ C₂ C₀ C₁' C₂' C₀' : Type*} [AddTorsor (PeriodGroup ω c) C₀]

/-- **A cylinder breaks into two cylinders.** The class of the composite of a cylinder `inner`
into an intermediate orbit followed by a cylinder `outer` out of it is the sum of the classes of
the two pieces, for any cap `D'` of the intermediate orbit. Only the equivariance of `outer` is
used. -/
theorem cylinderClass_comp [AddTorsor (PeriodGroup ω c) C₀'] (inner : C₁ → C₀')
    (outer : C₀' → C₀) (houter : ∀ (γ : PeriodGroup ω c) D', outer (γ +ᵥ D') = γ +ᵥ outer D')
    (D₁ : C₁) (D' : C₀') (D₀ : C₀) :
    cylinderClass (fun D₁ => outer (inner D₁)) D₁ D₀ =
      cylinderClass outer D' D₀ + cylinderClass inner D₁ D' := by
  -- sewing pairs of pants whose second inputs are the one-point type
  simpa only [productClass_eq_cylinderClass_fst] using
    productClass_comp_fst (fun D₁ (_ : Unit) => inner D₁) (fun D' (_ : Unit) => outer D')
      (fun γ D' _ => houter γ D') D₁ () () D' D₀

/-- **A pair of pants breaks off a cylinder at its output.** The class of a pair of pants `glue`
into an intermediate orbit followed by a cylinder `cyl` out of it is the class of the cylinder
plus the class of the pair of pants, for any cap `D'` of the intermediate orbit. Only the
equivariance of `cyl` is used. -/
theorem productClass_comp_out [AddTorsor (PeriodGroup ω c) C₀'] (glue : C₁ → C₂ → C₀')
    (cyl : C₀' → C₀) (hcyl : ∀ (γ : PeriodGroup ω c) D', cyl (γ +ᵥ D') = γ +ᵥ cyl D')
    (D₁ : C₁) (D₂ : C₂) (D' : C₀') (D₀ : C₀) :
    productClass (fun D₁ D₂ => cyl (glue D₁ D₂)) D₁ D₂ D₀ =
      cylinderClass cyl D' D₀ + productClass glue D₁ D₂ D' := by
  rw [productClass_eq_cylinderClass_snd, productClass_eq_cylinderClass_snd]
  exact cylinderClass_comp (glue D₁) cyl hcyl D₂ D' D₀

/-- **A pair of pants breaks off cylinders at its inputs.** The class of cylinders `cyl₁` and
`cyl₂` into the two inputs of a pair of pants `glue` is the class of the pair of pants plus the
classes of the two cylinders, for any caps `D₁'` and `D₂'` of the intermediate orbits. Only the
equivariance of `glue` in each input is used. A cylinder at a single input is the case where the
other cylinder is the identity, whose class at `D₂' = D₂` is zero. -/
theorem productClass_comp_in [AddTorsor (PeriodGroup ω c) C₁'] [AddTorsor (PeriodGroup ω c) C₂']
    (cyl₁ : C₁ → C₁') (cyl₂ : C₂ → C₂') (glue : C₁' → C₂' → C₀)
    (hglue₁ : ∀ (γ : PeriodGroup ω c) D₁ D₂, glue (γ +ᵥ D₁) D₂ = γ +ᵥ glue D₁ D₂)
    (hglue₂ : ∀ (γ : PeriodGroup ω c) D₁ D₂, glue D₁ (γ +ᵥ D₂) = γ +ᵥ glue D₁ D₂)
    (D₁ : C₁) (D₂ : C₂) (D₁' : C₁') (D₂' : C₂') (D₀ : C₀) :
    productClass (fun D₁ D₂ => glue (cyl₁ D₁) (cyl₂ D₂)) D₁ D₂ D₀ =
      productClass glue D₁' D₂' D₀ + cylinderClass cyl₁ D₁ D₁' + cylinderClass cyl₂ D₂ D₂' := by
  have h₁ := cylinderClass_comp cyl₁ (glue · D₂') (hglue₁ · · D₂') D₁ D₁' D₀
  have h₂ := cylinderClass_comp cyl₂ (glue (cyl₁ D₁)) (hglue₂ · (cyl₁ D₁)) D₂ D₂' D₀
  simp only [cylinderClass_def] at h₁ h₂
  rw [productClass_def, productClass_def, h₂, h₁, cylinderClass_def, cylinderClass_def]

end Breaking

end TauCeti.Floer
