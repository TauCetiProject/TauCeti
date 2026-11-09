/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.Skeleton.Induction
public import TauCeti.Topology.Homotopy.Cube.Radius
public import TauCeti.Topology.Homotopy.Extension.CWComplex
public import TauCeti.Topology.Homotopy.SerreFibration.RelativeCube

/-!
# Homotopy lifting over CW complexes for Serre fibrations

A Serre fibration is defined by lifting homotopies of disks. This file shows that it then lifts
homotopies of every CW complex, relative to any subcomplex: if `C` is a relative CW complex with
base `D`, a homotopy `I × C → B` lifts along a Serre fibration `p : E → B` to a homotopy
`I × C → E` extending any prescribed lift on `{0} × C ∪ I × D`
(`TauCeti.TopCat.exists_lift_relCWComplex_of_mem_serreFibrations`). In particular a Serre
fibration has the homotopy lifting property with respect to every CW complex
(`TauCeti.TopCat.hasHomotopyLiftingProperty_of_mem_serreFibrations`).

The lift is built one skeleton at a time, exactly as homotopies are extended over a relative CW
complex in the proof of the homotopy extension property.

* **One cell.** The characteristic maps of Mathlib's classical CW complexes are defined on the
  closed unit ball of the sup norm on `Fin n → ℝ`, which is the cube `Iⁿ` with its boundary
  sphere the boundary of the cube (`TauCeti.cubeHomeomorphClosedBall`). So relative lifting for
  the cube (`TauCeti.TopCat.exists_lift_openBox_of_mem_serreFibrations`) gives relative lifting
  for the closed ball with a prescribed lift on its bottom and boundary cylinder
  (`TauCeti.TopCat.exists_lift_closedBall_of_mem_serreFibrations`).
* **One skeleton.** A lift over `I × skeletonLT C n` is extended over each closed `n`-cell through
  its characteristic map, and these extensions glue to a lift over `I × skeletonLT C (n + 1)`
  (`TauCeti.TopCat.exists_lift_skeletonLT_succ_of_mem_serreFibrations`), by the weak topology of
  the complex (`TauCeti.exists_continuousMap_prod_skeletonLT_succ`).
* **All skeleta.** The successive lifts restrict to one another, so they glue to a lift over
  `I × C` (`TauCeti.exists_continuousMap_prod_complex_of_skeletonLT`).

No cell set or dimension is assumed finite, and the complex may be empty or have `0`-cells. The
fibration only has to lift homotopies of disks in its own universe, while the complex can live in
any universe.

## Main results

* `TauCeti.TopCat.exists_lift_closedBall_of_mem_serreFibrations`: relative lifting over a closed
  cell, with a prescribed lift on the bottom and boundary cylinder.
* `TauCeti.TopCat.exists_lift_skeletonLT_of_mem_serreFibrations`: relative lifting over a
  relative CW complex, with a prescribed lift on the bottom and over a skeleton.
* `TauCeti.TopCat.exists_lift_relCWComplex_of_mem_serreFibrations`: **a Serre fibration has the
  relative homotopy lifting property with respect to every relative CW complex.**
* `TauCeti.TopCat.hasHomotopyLiftingProperty_of_mem_serreFibrations`: a Serre fibration has the
  homotopy lifting property with respect to every CW complex.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.2, Proposition 4.48 (a Serre fibration has the homotopy lifting property with respect
  to all CW pairs).
* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I, Section 7.
-/

public section

noncomputable section

open CategoryTheory Metric Set Topology Topology.RelCWComplex unitInterval

universe u v

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B}

/-- **Relative lifting over a closed cell.** A Serre fibration lifts a homotopy of the closed unit
ball of the sup norm on `N → ℝ`, for a finite index type `N`, extending a prescribed lift on the
bottom `{0} × closedBall 0 1` and on the boundary cylinder `I × sphere 0 1`. This closed ball is
the domain of the characteristic maps of Mathlib's classical CW complexes. -/
theorem exists_lift_closedBall_of_mem_serreFibrations (hp : serreFibrations p) {N : Type v}
    [Fintype N] (f : C(cylinderExtensionDomain
      (Subtype.val ⁻¹' sphere (0 : N → ℝ) 1 : Set (closedBall (0 : N → ℝ) 1)), E))
    (H : C(I × closedBall (0 : N → ℝ) 1, B)) (hf : ∀ x, p (f x) = H x) :
    ∃ G : C(I × closedBall (0 : N → ℝ) 1, E), p ∘ G = H ∧
      ∀ x : cylinderExtensionDomain
        (Subtype.val ⁻¹' sphere (0 : N → ℝ) 1 : Set (closedBall (0 : N → ℝ) 1)), G x = f x := by
  -- Read the closed ball as the cube, whose boundary is the unit sphere.
  let e := cubeHomeomorphClosedBall N
  have he (y : N → I) : (e y : N → ℝ) ∈ sphere 0 1 ↔ y ∈ Cube.boundary N := by
    rw [mem_sphere_zero_iff_norm]
    exact norm_cubeHomeomorphClosedBall_eq_one_iff y
  let φ : C(I × (N → I), I × closedBall (0 : N → ℝ) 1) := ⟨fun x ↦ (x.1, e x.2), by fun_prop⟩
  let ψ : C(I × closedBall (0 : N → ℝ) 1, I × (N → I)) := ⟨fun x ↦ (x.1, e.symm x.2), by fun_prop⟩
  have hφψ (x : I × closedBall (0 : N → ℝ) 1) : φ (ψ x) = x := by
    simp [φ, ψ]
  have hφ (x : cylinderExtensionDomain (Cube.boundary N)) :
      φ x ∈ cylinderExtensionDomain
        (Subtype.val ⁻¹' sphere (0 : N → ℝ) 1 : Set (closedBall (0 : N → ℝ) 1)) :=
    mem_cylinderExtensionDomain_iff.2 ((mem_cylinderExtensionDomain_iff.1 x.2).imp id (he _).2)
  obtain ⟨G, hG, hGf⟩ := exists_lift_openBox_of_mem_serreFibrations hp N
    (f.comp ⟨fun x ↦ ⟨φ x, hφ x⟩, by fun_prop⟩) (H.comp φ) fun x ↦ hf _
  refine ⟨G.comp ψ, funext fun x ↦ ?_, fun x ↦ ?_⟩
  · simpa [hφψ] using congrFun hG (ψ x)
  · have hψ : ψ x ∈ cylinderExtensionDomain (Cube.boundary N) :=
      mem_cylinderExtensionDomain_iff.2 ((mem_cylinderExtensionDomain_iff.1 x.2).imp id fun h ↦
        (he (e.symm x.1.2)).1 (by simpa using h))
    simpa [hφψ] using hGf ⟨ψ x, hψ⟩

section CWComplex

variable {X : Type v} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]

section Cell

variable {n : ℕ}

/-- The characteristic map of an `n`-cell, as a map into the skeleton `skeletonLT C (n + 1)`. -/
private def cellSkeletonMap (j : cell C n) :
    C(closedBall (0 : Fin n → ℝ) 1, (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) :=
  ⟨fun y ↦ ⟨map n j y, map_mem_skeletonLT_succ j (mem_closedBall_zero_iff.1 y.2)⟩,
    (continuous_map_closedBall j).subtype_mk _⟩

/-- The characteristic map of an `n`-cell sends the boundary sphere into the `n`-skeleton. -/
private lemma cellSkeletonMap_mem_skeletonLT (j : cell C n) {y : closedBall (0 : Fin n → ℝ) 1}
    (hy : (y : Fin n → ℝ) ∈ sphere 0 1) : (cellSkeletonMap j y : X) ∈ (skeletonLT C n : Set X) :=
  cellFrontier_subset_skeletonLT n j ⟨y, hy, rfl⟩

/-- **Lifting over one closed `n`-cell.** Let `k` be a map on the cylinder of the
`(n + 1)`-skeleton that lifts `H` on the bottom and over the `n`-skeleton. Read through the
characteristic map of an `n`-cell, `H` lifts over the closed cell to a map agreeing with `k` on the
bottom and on the boundary cylinder. -/
private lemma exists_lift_cellSkeletonMap (hp : serreFibrations p) (j : cell C n)
    (k : C(I × (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X), E))
    (H : C(I × (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X), B))
    (hk₀ : ∀ x, p (k (0, x)) = H (0, x))
    (hk : ∀ t (x : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)),
      (x : X) ∈ (skeletonLT C n : Set X) → p (k (t, x)) = H (t, x)) :
    ∃ K : C(I × closedBall (0 : Fin n → ℝ) 1, E),
      (∀ z, p (K z) = H (z.1, cellSkeletonMap j z.2)) ∧
      ∀ z ∈ cylinderExtensionDomain
        (Subtype.val ⁻¹' sphere (0 : Fin n → ℝ) 1 : Set (closedBall (0 : Fin n → ℝ) 1)),
        K z = k (z.1, cellSkeletonMap j z.2) := by
  let ψ : C(I × closedBall (0 : Fin n → ℝ) 1, I × (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) :=
    ⟨fun z ↦ (z.1, cellSkeletonMap j z.2), by fun_prop⟩
  have hkψ (z : I × closedBall (0 : Fin n → ℝ) 1)
      (hz : z ∈ cylinderExtensionDomain
        (Subtype.val ⁻¹' sphere (0 : Fin n → ℝ) 1 : Set (closedBall (0 : Fin n → ℝ) 1))) :
      p (k (ψ z)) = H (ψ z) := by
    obtain ⟨t, y⟩ := z
    rcases mem_cylinderExtensionDomain_iff.1 hz with ht | hy
    · obtain rfl : t = 0 := ht
      exact hk₀ _
    · exact hk t _ (cellSkeletonMap_mem_skeletonLT j hy)
  obtain ⟨K, hK, hKk⟩ := exists_lift_closedBall_of_mem_serreFibrations hp
    ((k.comp ψ).restrict _) (H.comp ψ) fun z ↦ hkψ z.1 z.2
  exact ⟨K, fun z ↦ congrFun hK z, fun z hz ↦ hKk ⟨z, hz⟩⟩

end Cell

/-- **Relative lifting over one skeleton.** A Serre fibration lifts a homotopy of
`skeletonLT C (n + 1)` starting at a prescribed lift and extending a prescribed lift over
`skeletonLT C n`. -/
theorem exists_lift_skeletonLT_succ_of_mem_serreFibrations (hp : serreFibrations p) (n : ℕ)
    (f : C((skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X), E))
    (H : C(I × (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X), B)) (hH : ∀ x, H (0, x) = p (f x))
    (g : C(I × (Subtype.val ⁻¹' (skeletonLT C n : Set X) :
      Set (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)), E))
    (hg : ∀ t a, p (g (t, a)) = H (t, a)) (hgf : ∀ a, g (0, a) = f a) :
    ∃ G : C(I × (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X), E), p ∘ G = H ∧
      (∀ x, G (0, x) = f x) ∧ ∀ t (a : (Subtype.val ⁻¹' (skeletonLT C n : Set X) :
        Set (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X))), G (t, a) = g (t, a) := by
  -- Glue the two prescribed lifts to a map on the cylinder, by the homotopy extension property of
  -- the `n`-skeleton; only its values on `{0} × skeletonLT C (n + 1) ∪ I × skeletonLT C n` are
  -- used.
  have hHEP := hasHomotopyExtensionProperty_skeletonLT_succ (C := C) n
  obtain ⟨k, hk₀, hkg⟩ := hHEP.exists_extension_of_isClosed hHEP.isClosed f g hgf
  -- Lift over every closed `n`-cell, with the prescribed values on its bottom and boundary.
  choose K hKH hKk using fun j ↦ exists_lift_cellSkeletonMap hp j k H
    (fun x ↦ (congrArg p (hk₀ x)).trans (hH x).symm)
    fun t x hx ↦ (congrArg p (hkg t ⟨x, hx⟩)).trans (hg t ⟨x, hx⟩)
  -- Glue the lifts over the closed `n`-cells to the prescribed lift over the `n`-skeleton.
  let g' : C(I × (skeletonLT C n : Set X), E) :=
    g.comp ⟨fun z ↦ (z.1, ⟨⟨z.2, skeletonLT_mono (by exact_mod_cast n.le_succ) z.2.2⟩, z.2.2⟩),
      by fun_prop⟩
  obtain ⟨F, hFg, hFK⟩ := exists_continuousMap_prod_skeletonLT_succ g' K fun j t y hy ↦
    (hKk j (t, y) (mem_cylinderExtensionDomain_of_mem hy)).trans
      (hkg t ⟨_, cellSkeletonMap_mem_skeletonLT j hy⟩)
  -- Every point of the `(n + 1)`-skeleton lies in the `n`-skeleton or in an open `n`-cell.
  have hcases (x : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) :
      (∃ hx : (x : X) ∈ (skeletonLT C n : Set X), ∀ t, F (t, x) = g (t, ⟨x, hx⟩)) ∨
        ∃ (j : cell C n) (y : closedBall (0 : Fin n → ℝ) 1), cellSkeletonMap j y = x ∧
          ∀ t, F (t, x) = K j (t, y) := by
    rcases mem_skeletonLT_or_exists_map x.2 with hx | ⟨j, y, hy, hxy⟩
    · exact Or.inl ⟨hx, fun t ↦ hFg t x hx⟩
    · obtain rfl : x = cellSkeletonMap j ⟨y, mem_closedBall_zero_iff.2 hy.le⟩ :=
        Subtype.ext hxy.symm
      exact Or.inr ⟨j, _, rfl, fun t ↦ hFK j t _⟩
  refine ⟨F, funext fun z ↦ ?_, fun x ↦ ?_, fun t a ↦ hFg t a.1 a.2⟩
  · obtain ⟨t, x⟩ := z
    rcases hcases x with ⟨hx, hF⟩ | ⟨j, y, rfl, hF⟩
    · exact (congrArg p (hF t)).trans (hg _ _)
    · exact (congrArg p (hF t)).trans (hKH j _)
  · rcases hcases x with ⟨hx, hF⟩ | ⟨j, y, rfl, hF⟩
    · exact (hF 0).trans (hgf _)
    · exact (hF 0).trans ((hKk j (0, y) (zero_mem_cylinderExtensionDomain y)).trans (hk₀ _))

section Glue

variable {k : ℕ} {f : C(C, E)} {H : C(I × C, B)}
  {g : C(I × (Subtype.val ⁻¹' (skeletonLT C k : Set X) : Set C), E)}

variable (k f H g) in
/-- The solutions of the relative lifting problem `(f, H, g)` on the successive skeleta
`skeletonLT C (k + j)`, each obtained from the previous one by
`TauCeti.TopCat.exists_lift_skeletonLT_succ_of_mem_serreFibrations`. -/
private def liftSeq (hp : serreFibrations p) (hH : ∀ x, H (0, x) = p (f x))
    (hg : ∀ t a, p (g (t, a)) = H (t, a)) (hgf : ∀ a, g (0, a) = f a) : (j : ℕ) →
    {G : C(I × (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X), E) //
      (∀ z, p (G z) = H (z.1, ⟨z.2, (skeletonLT C _).subset_complex z.2.2⟩)) ∧
        ∀ x, G (0, x) = f ⟨x, (skeletonLT C _).subset_complex x.2⟩}
  | 0 => ⟨g.comp ⟨fun z ↦ (z.1, ⟨⟨z.2, (skeletonLT C _).subset_complex z.2.2⟩, z.2.2⟩),
      by fun_prop⟩, fun z ↦ hg _ _, fun x ↦ hgf _⟩
  | j + 1 =>
    have h := exists_lift_skeletonLT_succ_of_mem_serreFibrations (C := C) hp (k + j)
      (f.comp ⟨fun x ↦ ⟨x, (skeletonLT C _).subset_complex x.2⟩, by fun_prop⟩)
      (H.comp ⟨fun z ↦ (z.1, ⟨z.2, (skeletonLT C _).subset_complex z.2.2⟩), by fun_prop⟩)
      (fun x ↦ (hH _))
      ((liftSeq hp hH hg hgf j).1.comp ⟨fun z ↦ (z.1, ⟨z.2, z.2.2⟩), by fun_prop⟩)
      (fun t a ↦ (liftSeq hp hH hg hgf j).2.1 _) fun a ↦ (liftSeq hp hH hg hgf j).2.2 _
    ⟨h.choose, fun z ↦ congrFun h.choose_spec.1 z, h.choose_spec.2.1⟩

private lemma liftSeq_succ_apply {hp : serreFibrations p} {hH : ∀ x, H (0, x) = p (f x)}
    {hg : ∀ t a, p (g (t, a)) = H (t, a)} {hgf : ∀ a, g (0, a) = f a} (j : ℕ) (t : I)
    (x : X) (hx : x ∈ (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X)) :
    (liftSeq k f H g hp hH hg hgf (j + 1)).1
        (t, ⟨x, skeletonLT_mono (by exact_mod_cast (k + j).le_succ) hx⟩) =
      (liftSeq k f H g hp hH hg hgf j).1 (t, ⟨x, hx⟩) := by
  rw [liftSeq]
  exact (exists_lift_skeletonLT_succ_of_mem_serreFibrations (C := C) hp (k + j) _ _
    (fun x ↦ (hH _)) _ (fun t a ↦ (liftSeq k f H g hp hH hg hgf j).2.1 _)
    fun a ↦ (liftSeq k f H g hp hH hg hgf j).2.2 _).choose_spec.2.2 t
      ⟨⟨x, skeletonLT_mono (by exact_mod_cast (k + j).le_succ) hx⟩, hx⟩

end Glue

/-- **Relative lifting over a relative CW complex, relative to a skeleton.** A Serre fibration
lifts a homotopy of a relative CW complex `C` starting at a prescribed lift and extending a
prescribed lift over the skeleton `skeletonLT C k`. -/
theorem exists_lift_skeletonLT_of_mem_serreFibrations (hp : serreFibrations p) (k : ℕ)
    (f : C(C, E)) (H : C(I × C, B)) (hH : ∀ x, H (0, x) = p (f x))
    (g : C(I × (Subtype.val ⁻¹' (skeletonLT C k : Set X) : Set C), E))
    (hg : ∀ t a, p (g (t, a)) = H (t, a)) (hgf : ∀ a, g (0, a) = f a) :
    ∃ G : C(I × C, E), p ∘ G = H ∧ (∀ x, G (0, x) = f x) ∧
      ∀ t (a : (Subtype.val ⁻¹' (skeletonLT C k : Set X) : Set C)), G (t, a) = g (t, a) := by
  -- Solve the problem on the successive skeleta and glue the solutions.
  obtain ⟨G, hG⟩ := exists_continuousMap_prod_complex_of_skeletonLT
    (fun j ↦ (liftSeq k f H g hp hH hg hgf j).1) (liftSeq_succ_apply (hp := hp))
  refine ⟨G, funext fun z ↦ ?_, fun x ↦ ?_, fun t a ↦ hG 0 t a.1 a.2⟩
  · obtain ⟨t, x⟩ := z
    obtain ⟨j, hj⟩ := exists_mem_skeletonLT_add k x.2
    exact (congrArg p (hG j t x hj)).trans ((liftSeq k f H g hp hH hg hgf j).2.1 _)
  · obtain ⟨j, hj⟩ := exists_mem_skeletonLT_add k x.2
    exact (hG j 0 x hj).trans ((liftSeq k f H g hp hH hg hgf j).2.2 _)

/-- **A Serre fibration has the relative homotopy lifting property with respect to every relative
CW complex.** If `C` is a relative CW complex with base `D`, a homotopy `H : I × C → B` lifts along
a Serre fibration `p` to a homotopy `G : I × C → E` with prescribed initial lift `f` and
prescribed lift `g` over `I × D`, provided `f` and `g` agree at time `0`. -/
theorem exists_lift_relCWComplex_of_mem_serreFibrations (hp : serreFibrations p) (f : C(C, E))
    (H : C(I × C, B)) (hH : ∀ x, H (0, x) = p (f x)) (g : C(I × (Subtype.val ⁻¹' D : Set C), E))
    (hg : ∀ t a, p (g (t, a)) = H (t, a)) (hgf : ∀ a, g (0, a) = f a) :
    ∃ G : C(I × C, E), p ∘ G = H ∧ (∀ x, G (0, x) = f x) ∧
      ∀ t (a : (Subtype.val ⁻¹' D : Set C)), G (t, a) = g (t, a) := by
  -- The base is the `0`-skeleton.
  have hD (x : X) : x ∈ (skeletonLT C ((0 : ℕ) : ℕ∞) : Set X) ↔ x ∈ D := by
    rw [Nat.cast_zero, skeletonLT_zero_eq_base]
  obtain ⟨G, hGH, hGf, hGg⟩ := exists_lift_skeletonLT_of_mem_serreFibrations hp 0 f H hH
    (g.comp ⟨fun z ↦ (z.1, ⟨z.2, (hD _).1 z.2.2⟩), by fun_prop⟩) (fun t a ↦ hg _ _)
    fun a ↦ hgf _
  exact ⟨G, hGH, hGf, fun t a ↦ hGg t ⟨a, (hD _).2 a.2⟩⟩

/-- **A Serre fibration has the homotopy lifting property with respect to every CW complex.** -/
theorem hasHomotopyLiftingProperty_of_mem_serreFibrations (hp : serreFibrations p)
    [CWComplex C] : HasHomotopyLiftingProperty p C := by
  intro f H hH
  -- The base of a CW complex is empty, so there is no lift to prescribe over it.
  have h₀ (z : I × (Subtype.val ⁻¹' (∅ : Set X) : Set C)) : False := z.2.2
  obtain ⟨G, hGH, hGf, -⟩ := exists_lift_relCWComplex_of_mem_serreFibrations hp f H hH
    ⟨fun z ↦ (h₀ z).elim, continuous_of_const fun z ↦ (h₀ z).elim⟩ (fun t a ↦ (h₀ (t, a)).elim)
    fun a ↦ (h₀ (0, a)).elim
  exact ⟨G, hGH, hGf⟩

end CWComplex

end TopCat

end TauCeti
