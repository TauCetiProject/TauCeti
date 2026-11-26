/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Pi

/-!
# Kernel, range, cokernel, and powers of a coordinatewise linear map

For a family of linear maps `f i : M i → N i`, the coordinatewise map
`LinearMap.piMap f : (∀ i, M i) → (∀ i, N i)` acts on each coordinate separately. Its kernel and
its range are therefore the products of the kernels and of the ranges of the `f i`
(`LinearMap.ker_piMap`, `LinearMap.range_piMap`). This gives the kernel splitting
`ker (piMap f) ≃ ∀ i, ker (f i)` (`LinearMap.kerPiMapEquiv`) and, over a ring, the cokernel
splitting `(∀ i, N i) ⧸ range (piMap f) ≃ ∀ i, N i ⧸ range (f i)` (`LinearMap.cokerPiMapEquiv`),
for any index type. In particular a finite family of maps with finite kernels and cokernels has a
coordinatewise map with finite kernel and cokernel, and when these are free their ranks add
(`LinearMap.finrank_ker_piMap`, `LinearMap.finrank_quotient_range_piMap`).

Full dependent-product submodules `Submodule.pi Set.univ p` identify coordinatewise with
`∀ i, p i` (`Submodule.piUnivEquiv`) and are complementary if and only if they are complementary in
every coordinate (`Submodule.isCompl_pi_univ_iff`). Powers, bijectivity, and restricted bijectivity
of `LinearMap.piMap` likewise reduce coordinatewise (`LinearMap.piMap_pow`,
`LinearMap.bijective_piMap_iff`, `LinearMap.bijective_restrict_piMap_iff`).

These are the indexed-family analogues of the kernel, cokernel, and powers of a binary product
`LinearMap.prodMap`, and they compute the determinant line of a coordinatewise map of Fredholm
operators.
-/

public section

namespace Submodule

variable {R ι : Type*} {M : ι → Type*} [Semiring R] [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)]

/-- The linear equivalence between a full dependent-product submodule `Submodule.pi Set.univ p` and
the dependent product `∀ i, p i` of its coordinate submodules. -/
def piUnivEquiv (p : ∀ i, Submodule R (M i)) :
    ↥(pi Set.univ p) ≃ₗ[R] ∀ i, ↥(p i) where
  toFun x i := ⟨x.val i, x.property i trivial⟩
  invFun y := ⟨fun i ↦ (y i).val, fun i _ ↦ (y i).property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Evaluating `Submodule.piUnivEquiv` at coordinate `i` gives the `i`-th coordinate of `x`. -/
@[simp]
theorem coe_piUnivEquiv_apply (p : ∀ i, Submodule R (M i)) (x : ↥(pi Set.univ p)) (i : ι) :
    (piUnivEquiv p x i : M i) = x.val i :=
  (rfl)

/-- Evaluating `(Submodule.piUnivEquiv p).symm` at coordinate `i` gives the underlying value of
`y i`. -/
@[simp]
theorem coe_piUnivEquiv_symm_apply (p : ∀ i, Submodule R (M i)) (y : ∀ i, ↥(p i)) (i : ι) :
    ((piUnivEquiv p).symm y : ∀ i, M i) i = (y i : M i) :=
  (rfl)

/-- Two full dependent-product submodules `Submodule.pi Set.univ p` and `Submodule.pi Set.univ q`
are complementary if and only if `p i` and `q i` are complementary at every index `i`. -/
@[simp]
theorem isCompl_pi_univ_iff {p q : ∀ i, Submodule R (M i)} :
    IsCompl (pi Set.univ p) (pi Set.univ q) ↔ ∀ i, IsCompl (p i) (q i) := by
  classical
  simp only [isCompl_iff, disjoint_iff, codisjoint_iff, eq_bot_iff, eq_top_iff]
  refine ⟨fun ⟨hdisj, hcod⟩ i ↦ ⟨fun v hv ↦ ?_, fun v _ ↦ ?_⟩,
    fun h ↦ ⟨fun x hx ↦ funext fun i ↦
      (h i).1 ⟨hx.1 i trivial, hx.2 i trivial⟩, fun x _ ↦ ?_⟩⟩
  · have hsingle := hdisj ⟨le_comap_single_pi p hv.1, le_comap_single_pi q hv.2⟩
    simpa [LinearMap.single_apply] using congrFun hsingle i
  · obtain ⟨u, hu, w, hw, hEq⟩ :=
      mem_sup.mp (hcod (x := Pi.single i v) mem_top)
    exact mem_sup.mpr ⟨u i, hu i trivial, w i, hw i trivial,
      by simpa using congrFun hEq i⟩
  · choose u hu w hw huw using fun i ↦ mem_sup.mp ((h i).2 (x := x i) mem_top)
    exact mem_sup.mpr ⟨u, fun i _ ↦ hu i, w, fun i _ ↦ hw i, funext huw⟩

end Submodule

namespace LinearMap

section PowersAndBijectivity

variable {R ι : Type*} {M N : ι → Type*} [Semiring R] [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

/-- A power of a coordinatewise endomorphism of a dependent product is the coordinatewise map of
the powers. -/
@[simp]
theorem piMap_pow (f : ∀ i, Module.End R (M i)) (n : ℕ) :
    (piMap f : Module.End R (∀ i, M i)) ^ n = piMap fun i ↦ (f i) ^ n := by
  apply DFunLike.coe_injective
  simp only [FunLike.coe_pow_eq_iterate, coe_piMap, Pi.map_iterate]

/-- A coordinatewise linear map `LinearMap.piMap f` is bijective if and only if every coordinate
map `f i` is bijective. -/
theorem bijective_piMap_iff {f : ∀ i, M i →ₗ[R] N i} :
    Function.Bijective (piMap f) ↔ ∀ i, Function.Bijective (f i) := by
  classical
  refine ⟨fun ⟨hinj, hsurj⟩ i ↦ ⟨(Pi.map_injective.mp hinj) i, fun y ↦ ?_⟩, fun h ↦ .piMap h⟩
  obtain ⟨x, hx⟩ := hsurj (Pi.single i y)
  exact ⟨x i, by simpa using congrFun hx i⟩

/-- Restricting `LinearMap.piMap f` to `Submodule.pi Set.univ p` is bijective if and only if every
coordinate restriction `(f i).restrict` is bijective. -/
theorem bijective_restrict_piMap_iff {f : ∀ i, Module.End R (M i)}
    {p : ∀ i, Submodule R (M i)}
    {hp : ∀ x ∈ Submodule.pi Set.univ p, piMap f x ∈ Submodule.pi Set.univ p}
    {hpi : ∀ i, ∀ x ∈ p i, f i x ∈ p i} :
    Function.Bijective ((piMap f).restrict hp) ↔
      ∀ i, Function.Bijective ((f i).restrict (hpi i)) := by
  let e := Submodule.piUnivEquiv p
  have hcomp : ⇑e ∘ ⇑((piMap f).restrict hp) =
      ⇑(piMap fun i ↦ (f i).restrict (hpi i)) ∘ ⇑e := by
    funext x
    ext i
    simp [e]
  rw [← Function.Bijective.of_comp_iff' e.bijective, hcomp,
    Function.Bijective.of_comp_iff _ e.bijective, bijective_piMap_iff]

end PowersAndBijectivity

section Semiring

variable {R : Type*} [Semiring R] {ι : Type*} {M N : ι → Type*} [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
  (f : ∀ i, M i →ₗ[R] N i)

theorem mem_ker_piMap {x : ∀ i, M i} : x ∈ ker (piMap f) ↔ ∀ i, x i ∈ ker (f i) := by
  simp [funext_iff, Pi.map_apply]

/-- The kernel of a coordinatewise map is the product of the kernels. -/
@[simp]
theorem ker_piMap : ker (piMap f) = Submodule.pi Set.univ fun i ↦ ker (f i) := by
  ext x
  simp only [mem_ker_piMap, Submodule.mem_pi, Set.mem_univ, forall_const]

/-- The range of a coordinatewise map is the product of the ranges. -/
@[simp]
theorem range_piMap : range (piMap f) = Submodule.pi Set.univ fun i ↦ range (f i) :=
  SetLike.coe_injective <| by
    simpa only [coe_range, coe_piMap, Submodule.coe_pi] using Set.range_piMap fun i ↦ ⇑(f i)

/-- **The kernel of a coordinatewise map** is the product of the kernels of its components. -/
def kerPiMapEquiv : ker (piMap f) ≃ₗ[R] ∀ i, ker (f i) where
  toFun x i := ⟨x.val i, (mem_ker_piMap f).1 x.property i⟩
  invFun y := ⟨fun i ↦ y i, (mem_ker_piMap f).2 fun i ↦ (y i).property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_kerPiMapEquiv_apply (x : ker (piMap f)) (i : ι) :
    (kerPiMapEquiv f x i : M i) = (x : ∀ i, M i) i :=
  (rfl)

@[simp]
theorem coe_kerPiMapEquiv_symm_apply (y : ∀ i, ker (f i)) :
    ((kerPiMapEquiv f).symm y : ∀ i, M i) = fun i ↦ (y i : M i) :=
  (rfl)

instance [Finite ι] [∀ i, Module.Finite R (ker (f i))] : Module.Finite R (ker (piMap f)) :=
  Module.Finite.equiv (kerPiMapEquiv f).symm

/-- The kernel of a finite coordinatewise map has rank the sum of the ranks of the kernels of its
components. -/
@[simp]
theorem finrank_ker_piMap [Fintype ι] [StrongRankCondition R] [∀ i, Module.Free R (ker (f i))]
    [∀ i, Module.Finite R (ker (f i))] :
    Module.finrank R (ker (piMap f)) = ∑ i, Module.finrank R (ker (f i)) := by
  rw [(kerPiMapEquiv f).finrank_eq, Module.finrank_pi_fintype]

end Semiring

section Ring

variable {R : Type*} [Ring R] {ι : Type*} {M N : ι → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  (f : ∀ i, M i →ₗ[R] N i)

/-- **The cokernel of a coordinatewise map** is the product of the cokernels of its components:
the class of `y` goes to the family of the classes of the `y i` (`LinearMap.cokerPiMapEquiv_mk`). -/
noncomputable def cokerPiMapEquiv : ((∀ i, N i) ⧸ range (piMap f)) ≃ₗ[R] ∀ i, N i ⧸ range (f i) :=
  Submodule.quotEquivOfEq _ _ (by simp only [range_piMap, ker_piMap, Submodule.ker_mkQ]) ≪≫ₗ
    (piMap fun i ↦ (range (f i)).mkQ).quotKerEquivOfSurjective
      (by simpa using Function.Surjective.piMap fun i ↦ (range (f i)).mkQ_surjective)

@[simp]
theorem cokerPiMapEquiv_mk (y : ∀ i, N i) :
    cokerPiMapEquiv f (Submodule.Quotient.mk y) = fun i ↦ Submodule.Quotient.mk (y i) := by
  funext i
  simp [cokerPiMapEquiv]

@[simp]
theorem cokerPiMapEquiv_symm_apply (y : ∀ i, N i) :
    (cokerPiMapEquiv f).symm (fun i ↦ Submodule.Quotient.mk (y i)) = Submodule.Quotient.mk y := by
  rw [LinearEquiv.symm_apply_eq, cokerPiMapEquiv_mk]

instance [Finite ι] [∀ i, Module.Finite R (N i ⧸ range (f i))] :
    Module.Finite R ((∀ i, N i) ⧸ range (piMap f)) :=
  Module.Finite.equiv (cokerPiMapEquiv f).symm

/-- The cokernel of a finite coordinatewise map has rank the sum of the ranks of the cokernels of
its components. -/
@[simp]
theorem finrank_quotient_range_piMap [Fintype ι] [StrongRankCondition R]
    [∀ i, Module.Free R (N i ⧸ range (f i))] [∀ i, Module.Finite R (N i ⧸ range (f i))] :
    Module.finrank R ((∀ i, N i) ⧸ range (piMap f)) =
      ∑ i, Module.finrank R (N i ⧸ range (f i)) := by
  rw [(cokerPiMapEquiv f).finrank_eq, Module.finrank_pi_fintype]

end Ring

end LinearMap
