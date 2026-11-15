/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Sequential direct limits of modules along powers of an endomorphism

For an `R`-linear endomorphism `T` of a module `M`, the directed system indexed by `ℕ` with a copy
of `M` at each stage and transition maps `T ^ (j - i)` for `i ≤ j` has colimit
`Module.End.IterateDirectLimit T`, written `M[T⁻¹]` in representation theory and commutative
algebra. Passing from stage `i` to stage `i + 1` inverts the action of `T`: applying `T` at every
stage induces a linear automorphism `Module.End.iterateDirectLimitEquiv T` of the direct limit whose
inverse shifts stage `i` to stage `i + 1`.

Each stage map `Module.End.ofIterateDirectLimitStage T i` (in particular the stage-zero canonical
map `Module.End.toIterateDirectLimit T`) has kernel `⨆ k, LinearMap.ker (T ^ k)`, the submodule of
vectors annihilated by some power of `T`. Consequently:
* `M[T⁻¹]` is subsingleton if and only if `⨆ k, LinearMap.ker (T ^ k) = ⊤` (in particular whenever
  `T` is nilpotent, such as `T = 0`);
* the canonical map `M →ₗ[R] M[T⁻¹]` is injective (respectively bijective) if and only if `T` is
  injective (respectively bijective, such as `T = 1`).

Intertwining linear maps `f ∘ₗ T_M = T_N ∘ₗ f` induce linear maps between the corresponding direct
limits via `Module.End.iterateDirectLimitMap`.

## Main definitions

* `Module.End.IterateDirectLimit`: the `R`-module direct limit of `M` along powers of `T`.
* `Module.End.ofIterateDirectLimitStage` and `Module.End.toIterateDirectLimit`: the stage-`i` and
  stage-`0` canonical linear maps `M →ₗ[R] T.IterateDirectLimit`.
* `Module.End.iterateDirectLimitEquiv`: the canonical linear automorphism of `T.IterateDirectLimit`
  induced by `T`.
* `Module.End.toIterateDirectLimitEquivOfBijective`: the canonical linear isomorphism
  `M ≃ₗ[R] T.IterateDirectLimit` when `T` is bijective.
* `Module.End.iterateDirectLimitMap`: functoriality of `IterateDirectLimit` along intertwining maps.

## References

* D. Helm, *The Bernstein center of the category of smooth `W(k)[GL_n(F)]`-modules*,
  arXiv:1201.1874v3, Definition 11.9 and Lemma 11.10.
* J.-F. Dat, D. Helm, R. Kurinczuk, and G. Moss, *Finiteness for Hecke algebras of `p`-adic groups*,
  arXiv:2203.04929v2, Section 4.
-/

public section

namespace Module.End

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- The transition linear maps `T ^ (j - i)` (`i ≤ j`) of the sequential direct system of `M` along
powers of an endomorphism `T`. -/
def iterateDirectSystem (T : End R M) (i j : ℕ) (_ : i ≤ j) : M →ₗ[R] M :=
  T ^ (j - i)

@[simp]
theorem iterateDirectSystem_eq (T : End R M) (i j : ℕ) (hij : i ≤ j) :
    T.iterateDirectSystem i j hij = T ^ (j - i) :=
  (rfl)

instance instDirectedSystemIterateDirectSystem (T : End R M) :
    DirectedSystem (fun _ : ℕ ↦ M) (T.iterateDirectSystem · · ·) where
  map_self x := by simp
  map_map {k j i} hij hjk x := by
    simp only [iterateDirectSystem_eq, ← mul_apply_eq_comp, ← pow_add]
    have hsub : k - j + (j - i) = k - i := by omega
    rw [hsub]

/-- The sequential module direct limit `M[T⁻¹]` of copies of `M` indexed by `ℕ` along powers of
`T`. As an abbreviation for `Module.DirectLimit`, it inherits its module structure and universal
property directly from Mathlib. -/
abbrev IterateDirectLimit (T : End R M) : Type _ :=
  Module.DirectLimit (fun _ : ℕ ↦ M) T.iterateDirectSystem

/-- The canonical linear map from stage `i` of the iterate system into `T.IterateDirectLimit`. -/
noncomputable def ofIterateDirectLimitStage (T : End R M) (i : ℕ) :
    M →ₗ[R] T.IterateDirectLimit :=
  Module.DirectLimit.of R ℕ (fun _ ↦ M) T.iterateDirectSystem i

/-- Agreement of `ofIterateDirectLimitStage` with `Module.DirectLimit.of`. -/
theorem ofIterateDirectLimitStage_def (T : End R M) (i : ℕ) :
    T.ofIterateDirectLimitStage i =
      Module.DirectLimit.of R ℕ (fun _ ↦ M) T.iterateDirectSystem i :=
  (rfl)

/-- The canonical stage-zero linear map `M →ₗ[R] T.IterateDirectLimit`. -/
noncomputable def toIterateDirectLimit (T : End R M) : M →ₗ[R] T.IterateDirectLimit :=
  T.ofIterateDirectLimitStage 0

/-- `toIterateDirectLimit` is the stage-zero canonical map. -/
theorem toIterateDirectLimit_def (T : End R M) :
    T.toIterateDirectLimit = T.ofIterateDirectLimitStage 0 :=
  (rfl)

@[simp]
theorem ofIterateDirectLimitStage_pow_sub (T : End R M) {i j : ℕ} (hij : i ≤ j) (x : M) :
    T.ofIterateDirectLimitStage j ((T ^ (j - i)) x) = T.ofIterateDirectLimitStage i x := by
  simpa only [ofIterateDirectLimitStage_def, iterateDirectSystem_eq] using
    Module.DirectLimit.of_f (R := R) (ι := ℕ) (G := fun _ ↦ M) (f := T.iterateDirectSystem)
      (hij := hij) (x := x)

@[simp]
theorem ofIterateDirectLimitStage_add_pow (T : End R M) (i k : ℕ) (x : M) :
    T.ofIterateDirectLimitStage (i + k) ((T ^ k) x) = T.ofIterateDirectLimitStage i x := by
  simpa using T.ofIterateDirectLimitStage_pow_sub (Nat.le_add_right i k) x

@[simp]
theorem ofIterateDirectLimitStage_succ_apply (T : End R M) (i : ℕ) (x : M) :
    T.ofIterateDirectLimitStage (i + 1) (T x) = T.ofIterateDirectLimitStage i x := by
  simpa using T.ofIterateDirectLimitStage_add_pow i 1 x

@[simp]
theorem ofIterateDirectLimitStage_pow (T : End R M) (n : ℕ) (x : M) :
    T.ofIterateDirectLimitStage n ((T ^ n) x) = T.toIterateDirectLimit x := by
  simpa [toIterateDirectLimit_def] using T.ofIterateDirectLimitStage_add_pow 0 n x

/-- Every element of `T.IterateDirectLimit` is represented at some finite stage. -/
theorem exists_ofIterateDirectLimitStage (T : End R M) (z : T.IterateDirectLimit) :
    ∃ i x, T.ofIterateDirectLimitStage i x = z :=
  Module.DirectLimit.exists_of z

/-- A stage representative vanishes in `T.IterateDirectLimit` if and only if some power of `T`
annihilates it. -/
theorem ofIterateDirectLimitStage_eq_zero_iff {T : End R M} {i : ℕ} {x : M} :
    T.ofIterateDirectLimitStage i x = 0 ↔ ∃ k, (T ^ k) x = 0 := by
  constructor
  · intro h
    obtain ⟨j, _hij, hj⟩ := Module.DirectLimit.of.zero_exact h
    exact ⟨j - i, by simpa only [iterateDirectSystem_eq] using hj⟩
  · rintro ⟨k, hk⟩
    rw [← T.ofIterateDirectLimitStage_add_pow i k x, hk, map_zero]

/-- The kernel of every stage map into `T.IterateDirectLimit` is the ascending union of the kernels
of the powers of `T`. -/
@[simp]
theorem ker_ofIterateDirectLimitStage (T : End R M) (i : ℕ) :
    LinearMap.ker (T.ofIterateDirectLimitStage i) = ⨆ k, LinearMap.ker (T ^ k) := by
  ext x
  rw [LinearMap.mem_ker, ofIterateDirectLimitStage_eq_zero_iff,
    Submodule.mem_iSup_of_directed (fun k ↦ LinearMap.ker (T ^ k))
      T.iterateKer.monotone.directed_le]
  simp [LinearMap.mem_ker]

/-- The kernel of the canonical map `M →ₗ[R] T.IterateDirectLimit` is `⨆ k, ker (T ^ k)`. -/
@[simp]
theorem ker_toIterateDirectLimit (T : End R M) :
    LinearMap.ker T.toIterateDirectLimit = ⨆ k, LinearMap.ker (T ^ k) := by
  rw [toIterateDirectLimit_def, ker_ofIterateDirectLimitStage]

/-- A linear map `f : M →ₗ[R] N` intertwining `T_M` and `T_N` induces a linear map between their
iterate direct limits. -/
noncomputable def iterateDirectLimitMap {N : Type*} [AddCommMonoid N] [Module R N]
    {T_M : End R M} {T_N : End R N} (f : M →ₗ[R] N) (hf : f ∘ₗ T_M = T_N ∘ₗ f) :
    T_M.IterateDirectLimit →ₗ[R] T_N.IterateDirectLimit :=
  Module.DirectLimit.map (f := T_M.iterateDirectSystem) (f' := T_N.iterateDirectSystem)
    (fun _ ↦ f) fun i j _ ↦ by
      have hpow : ∀ k, f ∘ₗ (T_M ^ k) = (T_N ^ k) ∘ₗ f := fun k ↦ by
        induction k with
        | zero => simp [Module.End.one_eq_id]
        | succ k ih =>
          rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
            ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc, hf, ← LinearMap.comp_assoc]
      simpa only [iterateDirectSystem_eq] using hpow (j - i)

@[simp]
theorem iterateDirectLimitMap_ofIterateDirectLimitStage {N : Type*} [AddCommMonoid N] [Module R N]
    {T_M : End R M} {T_N : End R N} (f : M →ₗ[R] N) (hf : f ∘ₗ T_M = T_N ∘ₗ f) (i : ℕ) (x : M) :
    iterateDirectLimitMap f hf (T_M.ofIterateDirectLimitStage i x) =
      T_N.ofIterateDirectLimitStage i (f x) := by
  rw [iterateDirectLimitMap, ofIterateDirectLimitStage_def, ofIterateDirectLimitStage_def,
    Module.DirectLimit.map_apply_of]

@[simp]
theorem iterateDirectLimitMap_toIterateDirectLimit {N : Type*} [AddCommMonoid N] [Module R N]
    {T_M : End R M} {T_N : End R N} (f : M →ₗ[R] N) (hf : f ∘ₗ T_M = T_N ∘ₗ f) (x : M) :
    iterateDirectLimitMap f hf (T_M.toIterateDirectLimit x) = T_N.toIterateDirectLimit (f x) :=
  iterateDirectLimitMap_ofIterateDirectLimitStage f hf 0 x

/-- The canonical linear automorphism of `T.IterateDirectLimit` induced by `T`: it acts as `T` at
each stage, with inverse shifting stage `i` to stage `i + 1`. -/
noncomputable def iterateDirectLimitEquiv (T : End R M) :
    T.IterateDirectLimit ≃ₗ[R] T.IterateDirectLimit :=
  LinearEquiv.ofLinearMap
    (iterateDirectLimitMap T rfl)
    (Module.DirectLimit.lift R ℕ (fun _ ↦ M) T.iterateDirectSystem
      (fun i ↦ T.ofIterateDirectLimitStage (i + 1)) fun i j hij x ↦ by
        have hsub : j - i = (j + 1) - (i + 1) := by omega
        rw [iterateDirectSystem_eq, hsub]
        exact T.ofIterateDirectLimitStage_pow_sub (Nat.add_le_add_right hij 1) x)
    (Module.DirectLimit.hom_ext fun i ↦ LinearMap.ext fun x ↦ by
      rw [LinearMap.id_comp, LinearMap.comp_apply, LinearMap.comp_apply,
        Module.DirectLimit.lift_of, iterateDirectLimitMap_ofIterateDirectLimitStage,
        ofIterateDirectLimitStage_succ_apply, ofIterateDirectLimitStage_def])
    (Module.DirectLimit.hom_ext fun i ↦ LinearMap.ext fun x ↦ by
      rw [LinearMap.id_comp, LinearMap.comp_apply, LinearMap.comp_apply,
        ← ofIterateDirectLimitStage_def, iterateDirectLimitMap_ofIterateDirectLimitStage,
        ofIterateDirectLimitStage_def, Module.DirectLimit.lift_of,
        ofIterateDirectLimitStage_succ_apply, ofIterateDirectLimitStage_def])

@[simp]
theorem iterateDirectLimitEquiv_ofIterateDirectLimitStage (T : End R M) (i : ℕ) (x : M) :
    T.iterateDirectLimitEquiv (T.ofIterateDirectLimitStage i x) =
      T.ofIterateDirectLimitStage i (T x) := by
  rw [iterateDirectLimitEquiv, LinearEquiv.coe_ofLinearMap,
    iterateDirectLimitMap_ofIterateDirectLimitStage]

@[simp]
theorem iterateDirectLimitEquiv_toIterateDirectLimit (T : End R M) (x : M) :
    T.iterateDirectLimitEquiv (T.toIterateDirectLimit x) = T.toIterateDirectLimit (T x) :=
  T.iterateDirectLimitEquiv_ofIterateDirectLimitStage 0 x

@[simp]
theorem iterateDirectLimitEquiv_symm_ofIterateDirectLimitStage (T : End R M) (i : ℕ) (x : M) :
    T.iterateDirectLimitEquiv.symm (T.ofIterateDirectLimitStage i x) =
      T.ofIterateDirectLimitStage (i + 1) x := by
  rw [iterateDirectLimitEquiv, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap,
    ofIterateDirectLimitStage_def, Module.DirectLimit.lift_of]

/-- `T.IterateDirectLimit` is subsingleton if and only if every vector of `M` is annihilated by
some power of `T`. -/
theorem subsingleton_iterateDirectLimit_iff {T : End R M} :
    Subsingleton T.IterateDirectLimit ↔ (⨆ k, LinearMap.ker (T ^ k)) = ⊤ := by
  rw [subsingleton_iff_forall_eq 0, eq_top_iff]
  constructor
  · intro h x _
    rw [← ker_toIterateDirectLimit, LinearMap.mem_ker]
    exact h _
  · intro h z
    obtain ⟨i, x, rfl⟩ := T.exists_ofIterateDirectLimitStage z
    exact LinearMap.mem_ker.mp <| by
      rw [ker_ofIterateDirectLimitStage]
      exact h Submodule.mem_top

/-- The iterate direct limit of a nilpotent endomorphism is subsingleton. -/
theorem subsingleton_iterateDirectLimit_of_isNilpotent {T : End R M} (hT : IsNilpotent T) :
    Subsingleton T.IterateDirectLimit := by
  obtain ⟨c, hc⟩ := hT
  exact subsingleton_iterateDirectLimit_iff.mpr <| eq_top_iff.mpr fun x _ ↦
    Submodule.mem_iSup_of_mem c (by simp [hc])

instance instSubsingletonIterateDirectLimitZero : Subsingleton (0 : End R M).IterateDirectLimit :=
  subsingleton_iterateDirectLimit_of_isNilpotent IsNilpotent.zero

/-- The canonical map `M →ₗ[R] T.IterateDirectLimit` is injective if and only if `T` is
injective. -/
theorem injective_toIterateDirectLimit_iff {T : End R M} :
    Function.Injective T.toIterateDirectLimit ↔ Function.Injective T := by
  constructor
  · intro hinj x y hxy
    apply hinj
    rw [toIterateDirectLimit_def, ← T.ofIterateDirectLimitStage_succ_apply 0 x,
      ← T.ofIterateDirectLimitStage_succ_apply 0 y, hxy]
  · intro hinj x y hxy
    obtain ⟨j, _, hj⟩ := Module.DirectLimit.exists_eq_of_of_eq hxy
    exact hinj.iterate j (by simpa [iterateDirectSystem_eq, pow_apply_eq_iterate] using hj)

/-- The canonical map `M →ₗ[R] T.IterateDirectLimit` is bijective if and only if `T` is
bijective. -/
theorem bijective_toIterateDirectLimit_iff {T : End R M} :
    Function.Bijective T.toIterateDirectLimit ↔ Function.Bijective T := by
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨injective_toIterateDirectLimit_iff.mp hinj, fun y ↦ ?_⟩
    obtain ⟨x, hx⟩ := hsurj (T.ofIterateDirectLimitStage 1 y)
    refine ⟨x, hinj ?_⟩
    have h := congrArg T.iterateDirectLimitEquiv hx
    simpa [toIterateDirectLimit_def] using h
  · intro hbij
    let e : M ≃ₗ[R] M := LinearEquiv.ofBijective T hbij
    let g : End R M := e.symm.toLinearMap
    have hpow : ∀ k y, (T ^ k) ((g ^ k) y) = y := fun k ↦ by
      induction k with
      | zero => simp
      | succ k ih =>
        intro y
        rw [pow_succ', pow_succ, mul_apply_eq_comp, mul_apply_eq_comp, ih]
        exact e.apply_symm_apply y
    refine ⟨injective_toIterateDirectLimit_iff.mpr hbij.1, fun z ↦ ?_⟩
    obtain ⟨i, x, rfl⟩ := T.exists_ofIterateDirectLimitStage z
    exact ⟨(g ^ i) x, by rw [← T.ofIterateDirectLimitStage_pow i, hpow]⟩

/-- When `T` is bijective, the canonical map identifies `M` with `T.IterateDirectLimit`. -/
noncomputable def toIterateDirectLimitEquivOfBijective {T : End R M} (hT : Function.Bijective T) :
    M ≃ₗ[R] T.IterateDirectLimit :=
  LinearEquiv.ofBijective T.toIterateDirectLimit (bijective_toIterateDirectLimit_iff.mpr hT)

@[simp]
theorem toIterateDirectLimitEquivOfBijective_apply {T : End R M} (hT : Function.Bijective T)
    (x : M) :
    T.toIterateDirectLimitEquivOfBijective hT x = T.toIterateDirectLimit x :=
  (rfl)

end Module.End

end
