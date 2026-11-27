/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Homology.CyclesComplex
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
public import TauCeti.RingTheory.Flat.Extensions
import TauCeti.CategoryTheory.Exact.HomologicalComplex

/-!
# Flat cycles in complexes of modules

This file collects flatness criteria for the cycles `Z_i(K)` and cycle cokernels `K_i / Z_i(K)`
of complexes of modules over a commutative ring `R`.

* **Exact tails of bounded-above cochain complexes**
  (`CochainComplex.flat_cycles_of_exactAt_of_isStrictlyLE` and
  `CochainComplex.flat_opcycles_of_exactAt_of_isStrictlyLE`): in a bounded-above complex of flat
  modules, the cycles in degree `i` are flat if the complex is exact in all degrees strictly
  greater than `i` (no exactness in degree `i` is required); if exactness also holds in degree `i`,
  its opcycles are flat as well. This is the dimension-shifting step used when cutting off flat
  resolutions: the acyclic mapping cone of a quasi-isomorphism between bounded-above flat complexes
  has flat cycles. Only the terms at or above the cycle degree (strictly above the opcycle degree)
  need to be flat; nothing is assumed about the remaining terms.

* **Degreewise cycle and homology extensions**
  (`HomologicalComplex.flat_cyclesComplexShortComplex_X₁_X`,
  `HomologicalComplex.flat_cyclesComplexShortComplex_X₂_X`,
  `HomologicalComplex.flat_cyclesComplexShortComplex_X₃_X`,
  `HomologicalComplex.flat_map_eval_X₂`,
  `HomologicalComplex.flat_map_eval_X₃`,
  `HomologicalComplex.flat_cycles_of_flat_X_of_flat_cokernel`,
  `HomologicalComplex.flat_cycles_iff_flat_cokernel_iCycles_of_flat_homology`): for an arbitrary
  complex `K`, flatness of `Z_q(K)`, `K_q`, and `K_q / Z_q(K)` transfers to the terms of
  `K.cyclesComplexShortComplex` and its degreewise evaluations; the short exact sequence
  `0 ⟶ Z_q(K) ⟶ K_q ⟶ K_q / Z_q(K) ⟶ 0` makes `Z_q(K)` flat whenever `K_q` and `K_q / Z_q(K)` are
  flat; and for `c.Rel i j` the presentation `0 ⟶ K_i / Z_i(K) ⟶ Z_j(K) ⟶ H_j(K) ⟶ 0` shows that
  when `H_j(K)` is flat, `Z_j(K)` is flat if and only if `K_i / Z_i(K)` is flat.

* **Nonnegative chain complexes with flat homology**
  (`ChainComplex.flat_cokernel_iCycles_of_flat_homology`,
  `ChainComplex.flat_cycles_of_flat_homology`): in a chain complex indexed by `ℕ`, flatness of the
  terms and homology below degree `p` (at most `p` for `Z_p(K)`) implies flatness of `K_p / Z_p(K)`
  and `Z_p(K)` by induction on degree.

## References

* R. Hartshorne, *Algebraic Geometry*, Lemma III.12.3.
* D. Mumford, *Abelian Varieties*, §5, the lemma on complexes of flat modules.
-/

public section

open CategoryTheory Limits

universe u v

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- In a bounded-above complex flat in degrees `≥ i`, exactness strictly above `i` makes its
cycles in degree `i` flat. Exactness in degree `i` itself is not needed. -/
theorem flat_cycles_of_exactAt_of_isStrictlyLE (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (n i : ℤ) [K.IsStrictlyLE n] (hFlat : ∀ j, i ≤ j → Module.Flat R (K.X j))
    (hK : ∀ j, i < j → K.ExactAt j) : Module.Flat R (K.cycles i) := by
  have above (j : ℤ) (hj : n < j) : Module.Flat R (K.cycles j) := by
    have : Subsingleton (K.X j) := ModuleCat.subsingleton_of_isZero
      (K.isZero_of_isStrictlyLE n j hj)
    have : Subsingleton (K.cycles j) :=
      (ModuleCat.mono_iff_injective (K.iCycles j)).1 inferInstance |>.subsingleton
    infer_instance
  have step (j : ℤ) (hj : i ≤ j) [Module.Flat R (K.cycles (j + 1))] :
      Module.Flat R (K.cycles j) := by
    have := hFlat j hj
    have hS := K.cyclesShortComplex_shortExact j (j + 1) (by simp) (hK _ (by omega))
    rw [K.cyclesShortComplex_def] at hS
    exact Function.Exact.flat_left_of_injective_of_surjective
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact)
      hS.moduleCat_injective_f hS.moduleCat_surjective_g
  by_cases hi : n < i
  · exact above i hi
  -- Descend from the zero cycle module above the bound, one short exact cycle sequence at a time.
  have down (k : ℕ) (hk : i ≤ n + 1 - k) : Module.Flat R (K.cycles (n + 1 - k)) := by
    induction k with
    | zero =>
      have heq : n + 1 - (0 : ℕ) = n + 1 := by omega
      exact heq.symm ▸ above (n + 1) (by omega)
    | succ k ih =>
      have : Module.Flat R (K.cycles (n + 1 - k)) := ih (by omega)
      have heq : n + 1 - (k + 1 : ℕ) + 1 = n + 1 - k := by omega
      have : Module.Flat R (K.cycles (n + 1 - (k + 1 : ℕ) + 1)) := heq ▸ this
      exact step _ hk
  have heq : n + 1 - ((n + 1 - i).toNat : ℤ) = i := by omega
  exact heq ▸ down (n + 1 - i).toNat (by omega)

/-- In a bounded-above complex flat in degrees `> i` and exact in degrees `≥ i`, the quotient
in degree `i` by incoming boundaries is flat. This is the term introduced by canonical
truncation from below. -/
theorem flat_opcycles_of_exactAt_of_isStrictlyLE (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (n i : ℤ) [K.IsStrictlyLE n] (hFlat : ∀ j, i < j → Module.Flat R (K.X j))
    (hK : ∀ j, i ≤ j → K.ExactAt j) : Module.Flat R (K.opcycles i) := by
  have : Module.Flat R (K.cycles (i + 1)) :=
    K.flat_cycles_of_exactAt_of_isStrictlyLE n (i + 1)
      (fun j hj ↦ hFlat j (by omega)) (fun j hj ↦ hK j (by omega))
  -- Exactness in degree `i` identifies the kernel of the differential with incoming boundaries;
  -- corestricting the outgoing differential to cycles does not change its kernel.
  have hE := (K.exactAt_iff' (i - 1) i (i + 1) (by simp) (by simp)).mp (hK i le_rfl)
  have hS := K.exact_toCycles (i + 1) (K.d (i - 1) i) (K.d_comp_d _ _ _) hE
  have : Epi (K.toCycles i (i + 1)) :=
    HomologicalComplex.epi_toCycles_of_exactAt (hK (i + 1) (by omega)) (by simp)
  -- Both `opcycles i` and `cycles (i + 1)` are cokernels of `d (i - 1) i`.
  let e : K.opcycles i ≅ K.cycles (i + 1) :=
    (K.opcyclesIsCokernel (i - 1) i (by simp)).coconePointUniqueUpToIso hS.gIsCokernel
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

end CochainComplex

namespace HomologicalComplex

variable {R : Type u} [CommRing R]

/-- The degree-`q` term of `K.cyclesComplexShortComplex.X₁` is flat when `K.cycles q` is flat. -/
instance flat_cyclesComplexShortComplex_X₁_X {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} R) c) (q : ι) [Module.Flat R (K.cycles q)] :
    Module.Flat R (K.cyclesComplexShortComplex.X₁.X q) := by
  rw [cyclesComplexShortComplex_X₁, graded_X]
  infer_instance

/-- The degree-`q` term of `K.cyclesComplexShortComplex.X₂` is flat when `K.X q` is flat. -/
instance flat_cyclesComplexShortComplex_X₂_X {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} R) c) (q : ι) [Module.Flat R (K.X q)] :
    Module.Flat R (K.cyclesComplexShortComplex.X₂.X q) := by
  rw [cyclesComplexShortComplex_X₂]
  infer_instance

/-- The degree-`q` term of `K.cyclesComplexShortComplex.X₃` is flat when
`cokernel (K.iCycles q)` is flat. -/
instance flat_cyclesComplexShortComplex_X₃_X {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} R) c) (q : ι)
    [Module.Flat R (cokernel (K.iCycles q) : ModuleCat.{v} R)] :
    Module.Flat R (K.cyclesComplexShortComplex.X₃.X q) := by
  rw [cyclesComplexShortComplex_X₃, graded_X]
  infer_instance

/-- The middle term of `S.map (eval _ _ q)` is flat when `S.X₂.X q` is flat. -/
instance flat_map_eval_X₂ {ι : Type*} {c : ComplexShape ι}
    (S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) c)) (q : ι)
    [Module.Flat R (S.X₂.X q)] :
    Module.Flat R (S.map (eval _ _ q)).X₂ := by
  rw [ShortComplex.map_X₂, eval_obj]
  infer_instance

/-- The third term of `S.map (eval _ _ q)` is flat when `S.X₃.X q` is flat. -/
instance flat_map_eval_X₃ {ι : Type*} {c : ComplexShape ι}
    (S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) c)) (q : ι)
    [Module.Flat R (S.X₃.X q)] :
    Module.Flat R (S.map (eval _ _ q)).X₃ := by
  rw [ShortComplex.map_X₃, eval_obj]
  infer_instance

/-- If `K_q` and `K_q / Z_q(K)` are flat, then the cycles `Z_q(K)` are flat. -/
theorem flat_cycles_of_flat_X_of_flat_cokernel {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} R) c) (q : ι)
    [Module.Flat R (K.X q)] [Module.Flat R (cokernel (K.iCycles q) : ModuleCat.{v} R)] :
    Module.Flat R (K.cycles q) := by
  have hS := (shortExact_iff_degreewise_shortExact _).1 K.cyclesComplexShortComplex_shortExact q
  have hX₁ : Module.Flat R (K.cyclesComplexShortComplex.map (eval _ _ q)).X₁ :=
    Function.Exact.flat_left_of_injective_of_surjective
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS.exact)
      hS.moduleCat_injective_f hS.moduleCat_surjective_g
  rw [ShortComplex.map_X₁, eval_obj, cyclesComplexShortComplex_X₁, graded_X] at hX₁
  exact hX₁

/-- For `c.Rel i j`, if the homology `H_j(K)` is flat, then the cycles `Z_j(K)` are flat if and
only if the cycle cokernel `K_i / Z_i(K)` is flat. -/
theorem flat_cycles_iff_flat_cokernel_iCycles_of_flat_homology {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} R) c) (i j : ι) (hij : c.Rel i j)
    [Module.Flat R (K.homology j)] :
    Module.Flat R (K.cycles j) ↔ Module.Flat R (cokernel (K.iCycles i) : ModuleCat.{v} R) := by
  have hS := K.homologyPresentation_shortExact i j hij
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have : Module.Flat R (K.homologyPresentation i j hij).X₂ :=
      Module.Flat.of_linearEquiv (K.homologyPresentationX₂Iso i j hij).toLinearEquiv
    have : Module.Flat R (K.homologyPresentation i j hij).X₁ :=
      Function.Exact.flat_left_of_injective_of_surjective
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS.exact)
        hS.moduleCat_injective_f hS.moduleCat_surjective_g
    exact Module.Flat.of_linearEquiv (K.homologyPresentationX₁Iso i j hij).symm.toLinearEquiv
  · have : Module.Flat R (K.homologyPresentation i j hij).X₁ :=
      Module.Flat.of_linearEquiv (K.homologyPresentationX₁Iso i j hij).toLinearEquiv
    have : Module.Flat R (K.homologyPresentation i j hij).X₂ :=
      Function.Exact.flat_of_injective_of_surjective
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS.exact)
        hS.moduleCat_injective_f hS.moduleCat_surjective_g
    exact Module.Flat.of_linearEquiv (K.homologyPresentationX₂Iso i j hij).symm.toLinearEquiv

end HomologicalComplex

namespace ChainComplex

variable {R : Type u} [CommRing R]

/-- In a nonnegative chain complex whose terms and homology below degree `p` are flat, the cycle
cokernel `K_p / Z_p(K)` is flat. -/
theorem flat_cokernel_iCycles_of_flat_homology (K : ChainComplex (ModuleCat.{v} R) ℕ) (p : ℕ)
    (hX : ∀ q < p, Module.Flat R (K.X q)) (hH : ∀ q < p, Module.Flat R (K.homology q)) :
    Module.Flat R (cokernel (K.iCycles p) : ModuleCat.{v} R) := by
  induction p with
  | zero =>
    have h0 : IsZero (cokernel (K.iCycles 0)) := by
      have := K.isIso_iCycles 0 _ rfl (K.shape 0 _ (by simp))
      exact isZero_cokernel_of_epi _
    have := ModuleCat.subsingleton_of_isZero h0
    exact Module.Flat.of_free
  | succ p ih =>
    have := hX p (Nat.lt_succ_self p)
    have := hH p (Nat.lt_succ_self p)
    have := ih (fun q hq ↦ hX q (Nat.lt_succ_of_lt hq)) (fun q hq ↦ hH q (Nat.lt_succ_of_lt hq))
    have : Module.Flat R (K.cycles p) := K.flat_cycles_of_flat_X_of_flat_cokernel p
    exact (K.flat_cycles_iff_flat_cokernel_iCycles_of_flat_homology (p + 1) p (by simp)).1
      inferInstance

/-- In a nonnegative chain complex whose terms through degree `p` and homology below degree `p`
are flat, the cycles `Z_p(K)` are flat. -/
theorem flat_cycles_of_flat_homology (K : ChainComplex (ModuleCat.{v} R) ℕ) (p : ℕ)
    (hX : ∀ q ≤ p, Module.Flat R (K.X q)) (hH : ∀ q < p, Module.Flat R (K.homology q)) :
    Module.Flat R (K.cycles p) := by
  have := hX p le_rfl
  have := K.flat_cokernel_iCycles_of_flat_homology p (fun q hq ↦ hX q hq.le) hH
  exact K.flat_cycles_of_flat_X_of_flat_cokernel p

end ChainComplex
