/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Multilinear.Basis
public import TauCeti.RingTheory.NovikovModule.Grading
public import TauCeti.RingTheory.NovikovModule.Lattice
public import TauCeti.Topology.Algebra.Module.Multilinear.ModuleTopology

/-!
# Localization of multilinear maps on Novikov lattices

A multilinear map on a finite family of shifted lattices has a unique multilinear extension
over the full Novikov ring when the period map is surjective. The finite orbit bases of the
lattices become bases of the completed modules. We use Mathlib's `Basis.piTensorProduct` to
construct the extension and the potential topology to prove its continuity.

The shifted output lattice records the filtration loss of the map. Clearing denominators
in each input separately determines how that cutoff changes on the localized modules.
For the action period `(g, t) ↦ E g + t`, the lifts of real periods can be chosen as `(0, t)`.
The monomial formula then translates only the real coordinate of each output coefficient,
as read by `single_smul_apply`.
-/

public section

noncomputable section

namespace TauCeti.NovikovModule

open NovikovSeries

variable {R H : Type*} [CommRing R] [AddCommGroup H] {N : H →+ ℝ}
variable {α : Type*}
  {ι : α → Type*} [∀ i, Finite (ι i)] {P : ∀ i, ι i → Type*}
  [∀ i j, AddTorsor H (P i j)] {F : ∀ i, (Σ j, P i j) → ℝ}
  (hF : ∀ i j h (p : P i j), F i ⟨j, h +ᵥ p⟩ = F i ⟨j, p⟩ - N h)
variable {ι₀ : Type*} [Finite ι₀] {P₀ : ι₀ → Type*} [∀ j, AddTorsor H (P₀ j)]
  {F₀ : (Σ j, P₀ j) → ℝ}
  (hF₀ : ∀ j h (p : P₀ j), F₀ ⟨j, h +ᵥ p⟩ = F₀ ⟨j, p⟩ - N h)
variable {C : α → ℝ} {C₀ : ℝ}

local notation "Λ" => NovikovSeries R H N
local notation "Λ₀" => nonnegSubring R N

section Extension

variable [Finite α]

/-- Multilinear maps on the completed modules are determined by their values on any family of
shifted lattices whose cutoffs admit a lift in every orbit. -/
theorem multilinearMap_ext_lattice
    (hr : ∀ i j, ∃ p : P i j, F i ⟨j, p⟩ = C i) :
    letI : ∀ i, Module Λ (NovikovModule R (F i)) := fun i ↦ module (hF i)
    letI := module (R := R) hF₀
    ∀ {g g' : (Π i, NovikovModule R (F i)) →ₘₗ[Λ] NovikovModule R F₀},
      (∀ x : Π i, lattice R (hF i) (C i), g (fun i ↦ ↑(x i)) = g' (fun i ↦ ↑(x i))) →
      g = g' := by
  intro g g' heq
  let : ∀ i, Module Λ (NovikovModule R (F i)) := fun i ↦ module (hF i)
  let := module (R := R) hF₀
  choose r hr using hr
  apply Module.Basis.ext_multilinear (fun i ↦ basis (hF i) (r i))
  intro v
  simpa only [coe_latticeBasis] using heq (fun i ↦ latticeBasis (hF i) (r i) (hr i) (v i))

/-- Every multilinear map between shifted lattices extends uniquely to the completed modules
over the full Novikov ring, provided each source cutoff admits a lift in every orbit. -/
theorem existsUnique_localizeMultilinear
    (hr : ∀ i j, ∃ p : P i j, F i ⟨j, p⟩ = C i)
    (f : (Π i, lattice R (hF i) (C i)) →ₘₗ[Λ₀] lattice R hF₀ C₀) :
    letI : ∀ i, Module Λ (NovikovModule R (F i)) := fun i ↦ module (hF i)
    letI := module (R := R) hF₀
    ∃! g : (Π i, NovikovModule R (F i)) →ₘₗ[Λ] NovikovModule R F₀,
      ∀ x : Π i, lattice R (hF i) (C i), g (fun i ↦ ↑(x i)) = ↑(f x) := by
  let : ∀ i, Module Λ (NovikovModule R (F i)) := fun i ↦ module (hF i)
  let := module (R := R) hF₀
  choose r hr' using hr
  let b i := basis (R := R) (hF i) (r i)
  let b₀ i := latticeBasis (R := R) (hF i) (r i) (hr' i)
  let L := (Basis.piTensorProduct b).constr Λ
    (fun v ↦ (f (fun i ↦ b₀ i (v i)) : NovikovModule R F₀))
  let g := L.compMultilinearMap (PiTensorProduct.tprod Λ)
  have hg : ∀ x : Π i, lattice R (hF i) (C i), g (fun i ↦ ↑(x i)) = ↑(f x) := by
    let g₀ := (g.restrictScalars Λ₀).compLinearMap (fun i ↦ (lattice R (hF i) (C i)).subtype)
    have hg₀ : g₀ = (lattice R hF₀ C₀).subtype.compMultilinearMap f := by
      apply Module.Basis.ext_multilinear b₀
      intro v
      simp only [g₀, g, MultilinearMap.compLinearMap_apply, MultilinearMap.coe_restrictScalars,
        LinearMap.compMultilinearMap_apply, Submodule.subtype_apply, b₀, coe_latticeBasis]
      rw [← Basis.piTensorProduct_apply b]
      exact (Basis.piTensorProduct b).constr_basis Λ _ v
    exact fun x ↦ MultilinearMap.congr_fun hg₀ x
  exact ⟨g, hg, fun g' hg' ↦
    multilinearMap_ext_lattice hF hF₀ (fun i j ↦ ⟨r i j, hr' i j⟩) fun x ↦
      (hg' x).trans (hg x).symm⟩

/-- The extension of a lattice multilinear map to the completed modules over the full Novikov
ring. Surjectivity of the period gives lifts at every source cutoff. -/
def localizeMultilinear (hN : Function.Surjective N)
    (f : (Π i, lattice R (hF i) (C i)) →ₘₗ[Λ₀] lattice R hF₀ C₀) :
    letI : ∀ i, Module Λ (NovikovModule R (F i)) := fun i ↦ module (hF i)
    letI := module (R := R) hF₀
    (Π i, NovikovModule R (F i)) →ₘₗ[Λ] NovikovModule R F₀ :=
  (existsUnique_localizeMultilinear hF hF₀
    (fun i j ↦ exists_potential_eq (hF i) hN j (C i)) f).exists.choose

/-- The localized map agrees with the given map on lattice inputs. -/
@[simp]
theorem localizeMultilinear_apply_coe (hN : Function.Surjective N)
    (f : (Π i, lattice R (hF i) (C i)) →ₘₗ[Λ₀] lattice R hF₀ C₀)
    (x : Π i, lattice R (hF i) (C i)) :
    localizeMultilinear hF hF₀ hN f (fun i ↦ ↑(x i)) = ↑(f x) :=
  (existsUnique_localizeMultilinear hF hF₀
    (fun i j ↦ exists_potential_eq (hF i) hN j (C i)) f).exists.choose_spec x

/-- The multilinear extension is continuous for the potential topology on the completed
modules. -/
@[fun_prop]
theorem continuous_localizeMultilinear (hN : Function.Surjective N)
    (f : (Π i, lattice R (hF i) (C i)) →ₘₗ[Λ₀] lattice R hF₀ C₀) :
    Continuous (localizeMultilinear hF hF₀ hN f) := by
  let : ∀ i, Module Λ (NovikovModule R (F i)) := fun i ↦ module (hF i)
  let := module (R := R) hF₀
  let : ∀ i, IsModuleTopology Λ (NovikovModule R (F i)) := fun i ↦
    IsModuleTopology.iso (coordinatesContinuousLinearEquiv (hF i)
      (fun j ↦ Classical.arbitrary (P i j))).symm
  let : ∀ i, Module.Finite Λ (NovikovModule R (F i)) := fun i ↦
    Module.Finite.of_basis (basis (hF i) (fun j ↦ Classical.arbitrary (P i j)))
  let : ContinuousSMul Λ (NovikovModule R F₀) := continuousSMul_module hF₀
  exact IsModuleTopology.continuous_multilinearMap (localizeMultilinear hF hF₀ hN f)

/-- A multilinear map over the full Novikov ring comes from a unique map on the given lattices
exactly when it sends their product into the target lattice. -/
theorem existsUnique_localizeMultilinear_eq_iff (hN : Function.Surjective N) :
    letI : ∀ i, Module Λ (NovikovModule R (F i)) := fun i ↦ module (hF i)
    letI := module (R := R) hF₀
    ∀ g : (Π i, NovikovModule R (F i)) →ₘₗ[Λ] NovikovModule R F₀,
      (∃! f : (Π i, lattice R (hF i) (C i)) →ₘₗ[Λ₀] lattice R hF₀ C₀,
        localizeMultilinear hF hF₀ hN f = g) ↔
      ∀ x : Π i, lattice R (hF i) (C i), g (fun i ↦ ↑(x i)) ∈ lattice R hF₀ C₀ := by
  let : ∀ i, Module Λ (NovikovModule R (F i)) := fun i ↦ module (hF i)
  let := module (R := R) hF₀
  intro g
  constructor
  · rintro ⟨f, rfl, -⟩ x
    rw [localizeMultilinear_apply_coe]
    exact (f x).property
  · intro hg
    let g₀ := (g.restrictScalars Λ₀).compLinearMap (fun i ↦ (lattice R (hF i) (C i)).subtype)
    let f := g₀.codRestrict (lattice R hF₀ C₀) hg
    have hval (x : Π i, lattice R (hF i) (C i)) :
        (f x : NovikovModule R F₀) = g (fun i ↦ ↑(x i)) := by
      simpa only [LinearMap.compMultilinearMap_apply, Submodule.subtype_apply, g₀,
        MultilinearMap.compLinearMap_apply, MultilinearMap.coe_restrictScalars] using
        MultilinearMap.congr_fun (LinearMap.subtype_compMultilinearMap_codRestrict g₀ _ hg) x
    refine ⟨f, multilinearMap_ext_lattice hF hF₀
      (fun i j ↦ exists_potential_eq (hF i) hN j (C i)) ?_, fun f' hf' ↦ ?_⟩
    · intro x
      rw [localizeMultilinear_apply_coe, hval]
    · apply MultilinearMap.ext
      intro x
      apply Subtype.ext
      rw [← localizeMultilinear_apply_coe hF hF₀ hN f', hf', hval]

end Extension

section Denominators

variable [Fintype α] (hN : Function.Surjective N)

/-- To evaluate the extension, multiply each input by a monomial that sends it into its source
lattice, apply the given map, then multiply the result by the product of the inverse monomials. -/
theorem localizeMultilinear_apply_of_single_smul_mem_lattice
    (f : (Π i, lattice R (hF i) (C i)) →ₘₗ[Λ₀] lattice R hF₀ C₀) (h : α → H) :
    letI : ∀ i, Module Λ (NovikovModule R (F i)) := fun i ↦ module (hF i)
    letI := module (R := R) hF₀
    ∀ (x : ∀ i, NovikovModule R (F i))
      (hx : ∀ i, NovikovSeries.single (N := N) (h i) (1 : R) • x i ∈ lattice R (hF i) (C i)),
      localizeMultilinear hF hF₀ hN f x =
        NovikovSeries.single (N := N) (-(∑ i, h i)) (1 : R) •
          (f (fun i ↦ ⟨_, hx i⟩) : NovikovModule R F₀) := by
  let : ∀ i, Module Λ (NovikovModule R (F i)) := fun i ↦ module (hF i)
  let := module (R := R) hF₀
  intro x hx
  let y : ∀ i, lattice R (hF i) (C i) := fun i ↦ ⟨_, hx i⟩
  have hy (i : α) :
      NovikovSeries.single (N := N) (-h i) (1 : R) • (y i : NovikovModule R (F i)) = x i := by
    simp only [y, smul_smul, single_mul_single, neg_add_cancel, mul_one, single_zero_one, one_smul]
  have hprod (s : Finset α) :
      (∏ i ∈ s, NovikovSeries.single (N := N) (-h i) (1 : R)) =
        NovikovSeries.single (-(∑ i ∈ s, h i)) 1 := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [single_zero_one]
    | insert i s hi ih =>
      simp [hi, ih, single_mul_single, add_comm]
  simpa only [hy, localizeMultilinear_apply_coe, RingHom.id_apply, hprod] using
    (localizeMultilinear hF hF₀ hN f).map_smul_univ
      (fun i ↦ NovikovSeries.single (N := N) (-h i) (1 : R)) (fun i ↦ ↑(y i))

/-- Localization preserves the energy-loss bound encoded by the original cutoffs. Changing
each input cutoff from `C i` to `D i` changes the output cutoff by the sum of these differences. -/
theorem localizeMultilinear_mem_lattice
    (f : (Π i, lattice R (hF i) (C i)) →ₘₗ[Λ₀] lattice R hF₀ C₀)
    (D : α → ℝ) (x : ∀ i, NovikovModule R (F i))
    (hx : ∀ i, x i ∈ lattice R (hF i) (D i)) :
    localizeMultilinear hF hF₀ hN f x ∈ lattice R hF₀ (C₀ + ∑ i, (D i - C i)) := by
  let : ∀ i, Module Λ (NovikovModule R (F i)) := fun i ↦ module (hF i)
  let := module (R := R) hF₀
  choose h hh using fun i ↦ hN (D i - C i)
  have hx' (i : α) :
      NovikovSeries.single (N := N) (h i) (1 : R) • x i ∈ lattice R (hF i) (C i) := by
    rw [single_smul_mem_lattice_iff, hh, add_comm (C i), sub_add_cancel]
    exact hx i
  rw [localizeMultilinear_apply_of_single_smul_mem_lattice hF hF₀ hN f h x hx', mem_lattice]
  have hp := NovikovSeries.single_mem_periodFiltration (N := N) (-(∑ i, h i)) (1 : R)
  simp only [map_neg, map_sum, hh] at hp
  rw [← sub_neg_eq_add]
  exact smul_mem_potentialFiltration_sub hF₀ hp ((mem_lattice hF₀).mp (f _).property)

variable {B : Type*} [AddCommGroup B]
  (δ : H →+ B) {d : ∀ i, (Σ j, P i j) → B} {d₀ : (Σ j, P₀ j) → B}
  (hd : ∀ i j h (p : P i j), d i ⟨j, h +ᵥ p⟩ = δ h + d i ⟨j, p⟩)
  (hd₀ : ∀ j h (p : P₀ j), d₀ ⟨j, h +ᵥ p⟩ = δ h + d₀ ⟨j, p⟩)

include hd hd₀ in
/-- A lattice map homogeneous of degree `ε` remains homogeneous of that degree after
localization. The degree shifts of the input monomials cancel those of their inverses. -/
theorem localizeMultilinear_mem_gradeBy
    (f : (Π i, lattice R (hF i) (C i)) →ₘₗ[Λ₀] lattice R hF₀ C₀) (ε : B)
    (hf : ∀ (b : α → B) (y : Π i, lattice R (hF i) (C i)),
      (∀ i, (y i : NovikovModule R (F i)) ∈ gradeBy R (F i) (d i) (b i)) →
      (f y : NovikovModule R F₀) ∈ gradeBy R F₀ d₀ ((∑ i, b i) + ε))
    (b : α → B) (x : ∀ i, NovikovModule R (F i))
    (hx : ∀ i, x i ∈ gradeBy R (F i) (d i) (b i)) :
    localizeMultilinear hF hF₀ hN f x ∈ gradeBy R F₀ d₀ ((∑ i, b i) + ε) := by
  let : ∀ i, Module Λ (NovikovModule R (F i)) := fun i ↦ module (hF i)
  let := module (R := R) hF₀
  choose D hD using fun i ↦ exists_mem_potentialFiltration (R := R) (F := F i) (x i)
  choose h hh using fun i ↦ hN (D i - C i)
  have hx' (i : α) :
      NovikovSeries.single (N := N) (h i) (1 : R) • x i ∈ lattice R (hF i) (C i) := by
    rw [single_smul_mem_lattice_iff, hh, add_comm (C i), sub_add_cancel, mem_lattice]
    exact hD i
  rw [localizeMultilinear_apply_of_single_smul_mem_lattice hF hF₀ hN f h x hx']
  have hy := hf (fun i ↦ δ (h i) + b i) (fun i ↦ ⟨_, hx' i⟩) fun i ↦
    smul_mem_gradeBy (hF i) δ (hd i) (NovikovSeries.single_mem_gradeBy δ (h i) (1 : R)) (hx i)
  have hp := NovikovSeries.single_mem_gradeBy (R := R) (N := N) δ (-(∑ i, h i)) 1
  simpa only [map_neg, map_sum, Finset.sum_add_distrib, ← add_assoc, neg_add_cancel, zero_add]
    using smul_mem_gradeBy hF₀ δ hd₀ hp hy

end Denominators

end TauCeti.NovikovModule
