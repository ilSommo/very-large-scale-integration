import pygame
import colorsys
BLACK = (0, 0, 0)
WHITE = (255, 255, 255)

def drawGrid(WINDOW_WIDTH, WINDOW_HEIGHT):
    blockSize = 20 #Set the size of the grid block
    for x in range(0, WINDOW_WIDTH, blockSize):
        for y in range(0, WINDOW_HEIGHT, blockSize):
            rect = pygame.Rect(x, y, blockSize, blockSize)
            pygame.draw.rect(SCREEN, BLACK, rect, 1)

def main(i):
    file = 'out/out-' + str(i)
    with open(file+'.txt', 'r') as infile:
        line_split = infile.readline().strip().split(' ')
        WIDTH, HEIGHT = int(line_split[0]), int(line_split[1])
        N = int(infile.readline().strip())
        BLOCKS = []
        line = infile.readline()
        while line.strip():
            line_split = (line.strip().split(' '))
            BLOCKS.append((int(line_split[0]),int(line_split[1]),int(line_split[2]),int(line_split[3])))
            line = infile.readline()
    WINDOW_WIDTH = 20*WIDTH
    WINDOW_HEIGHT = 20*HEIGHT

    print(BLOCKS)

    global SCREEN, CLOCK
    pygame.init()
    SCREEN = pygame.display.set_mode((WINDOW_WIDTH, WINDOW_HEIGHT))
    CLOCK = pygame.time.Clock()
    SCREEN.fill(WHITE)

    for j in range(N):
        block = BLOCKS[j]
        rect = pygame.Rect(block[2]*20, WINDOW_HEIGHT-block[3]*20-block[1]*20, block[0]*20, block[1]*20)
        color = colorsys.hsv_to_rgb(j/N,0.75,191)
        pygame.draw.rect(SCREEN, color, rect, 0)
    
    drawGrid(WINDOW_WIDTH, WINDOW_HEIGHT)

    pygame.display.update()

    pygame.image.save(SCREEN, "out/out-"+str(i)+".png")

for i in range(1,11):
    main(i)